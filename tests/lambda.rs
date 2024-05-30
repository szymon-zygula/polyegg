use egg::{rewrite_par as rwp, *};
use fxhash::FxHashSet as HashSet;

define_language! {
    enum Lambda {
        Bool(bool),
        Num(i32),

        "var" = Var(Id),

        "+" = Add([Id; 2]),
        "=" = Eq([Id; 2]),

        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),
        "let" = Let([Id; 3]),
        "fix" = Fix([Id; 2]),

        "if" = If([Id; 3]),

        Symbol(egg::Symbol),
    }
}

impl Lambda {
    fn num(&self) -> Option<i32> {
        match self {
            Lambda::Num(n) => Some(*n),
            _ => None,
        }
    }
}

type EGraph = egg::EGraph<Lambda, LambdaAnalysis>;

#[derive(Default)]
struct LambdaAnalysis;

#[derive(Debug)]
struct Data {
    free: HashSet<Id>,
    constant: Option<(Lambda, PatternAst<Lambda>)>,
}

fn eval(egraph: &EGraph, enode: &Lambda) -> Option<(Lambda, PatternAst<Lambda>)> {
    let x = |i: &Id| egraph[*i].data.constant.as_ref().map(|c| &c.0);
    match enode {
        Lambda::Num(n) => Some((enode.clone(), format!("{}", n).parse().unwrap())),
        Lambda::Bool(b) => Some((enode.clone(), format!("{}", b).parse().unwrap())),
        Lambda::Add([a, b]) => Some((
            Lambda::Num(x(a)?.num()?.checked_add(x(b)?.num()?)?),
            format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        Lambda::Eq([a, b]) => Some((
            Lambda::Bool(x(a)? == x(b)?),
            format!("(= {} {})", x(a)?, x(b)?).parse().unwrap(),
        )),
        _ => None,
    }
}

impl Analysis<Lambda> for LambdaAnalysis {
    type Data = Data;
    fn merge(&mut self, to: &mut Data, from: Data) -> DidMerge {
        let before_len = to.free.len();
        // to.free.extend(from.free);
        to.free.retain(|i| from.free.contains(i));
        // compare lengths to see if I changed to or from
        DidMerge(
            before_len != to.free.len(),
            to.free.len() != from.free.len(),
        ) | merge_option(&mut to.constant, from.constant, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn make(egraph: &EGraph, enode: &Lambda) -> Data {
        let f = |i: &Id| egraph[*i].data.free.iter().cloned();
        let mut free = HashSet::default();
        match enode {
            Lambda::Var(v) => {
                free.insert(*v);
            }
            Lambda::Let([v, a, b]) => {
                free.extend(f(b));
                free.remove(v);
                free.extend(f(a));
            }
            Lambda::Lambda([v, a]) | Lambda::Fix([v, a]) => {
                free.extend(f(a));
                free.remove(v);
            }
            _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
        }
        let constant = eval(egraph, enode);
        Data { constant, free }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.constant.clone() {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &c.0.to_string().parse().unwrap(),
                    &c.1,
                    &Default::default(),
                    "analysis".to_string(),
                );
            } else {
                let const_id = egraph.add(c.0);
                egraph.union(id, const_id);
            }
        }
    }
}

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

struct IsNotSameVar {
    v1: Var,
    v2: Var,
}

impl IsNotSameVar {
    pub fn new(v1: Var, v2: Var) -> Self {
        Self { v1, v2 }
    }
}

impl Condition<Lambda, LambdaAnalysis> for IsNotSameVar {
    fn check(
        &self,
        egraph: &mut egg::EGraph<Lambda, LambdaAnalysis>,
        eclass: Id,
        subst: &Subst,
    ) -> bool {
        self.check_const(egraph, eclass, subst)
    }
}

impl ConstCondition<Lambda, LambdaAnalysis> for IsNotSameVar {
    fn check_const(
        &self,
        egraph: &egg::EGraph<Lambda, LambdaAnalysis>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        egraph.find(subst[self.v1]) != egraph.find(subst[self.v2])
    }
}

struct IsConst {
    v: Var,
}

impl IsConst {
    pub fn new(v: Var) -> Self {
        Self { v }
    }
}

impl Condition<Lambda, LambdaAnalysis> for IsConst {
    fn check(
        &self,
        egraph: &mut egg::EGraph<Lambda, LambdaAnalysis>,
        eclass: Id,
        subst: &Subst,
    ) -> bool {
        self.check_const(egraph, eclass, subst)
    }
}

impl ConstCondition<Lambda, LambdaAnalysis> for IsConst {
    fn check_const(
        &self,
        egraph: &egg::EGraph<Lambda, LambdaAnalysis>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        egraph[subst[self.v]].data.constant.is_some()
    }
}

fn rules() -> Vec<ParallelRewrite<Lambda, LambdaAnalysis>> {
    vec![
        // open term rules
        rwp!("if-true";  "(if  true ?then ?else)" => "?then"),
        rwp!("if-false"; "(if false ?then ?else)" => "?else"),
        // rwp!("if-elim"; "(if (= (var ?x) ?e) ?then ?else)" => "?else"
        //     if ConditionEqual::parse("(let ?x ?e ?then)", "(let ?x ?e ?else)")),
        rwp!("add-comm";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rwp!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rwp!("eq-comm";   "(= ?a ?b)"        => "(= ?b ?a)"),
        // subst rules
        rwp!("fix";      "(fix ?v ?e)"             => "(let ?v (fix ?v ?e) ?e)"),
        rwp!("beta";     "(app (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rwp!("let-app";  "(let ?v ?e (app ?a ?b))" => "(app (let ?v ?e ?a) (let ?v ?e ?b))"),
        rwp!("let-add";  "(let ?v ?e (+   ?a ?b))" => "(+   (let ?v ?e ?a) (let ?v ?e ?b))"),
        rwp!("let-eq";   "(let ?v ?e (=   ?a ?b))" => "(=   (let ?v ?e ?a) (let ?v ?e ?b))"),
        rwp!("let-const";
            "(let ?v ?e ?c)" => "?c" if IsConst::new(var("?c"))),
        rwp!("let-if";
            "(let ?v ?e (if ?cond ?then ?else))" =>
            "(if (let ?v ?e ?cond) (let ?v ?e ?then) (let ?v ?e ?else))"
        ),
        rwp!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
        rwp!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
            if IsNotSameVar::new(var("?v1"), var("?v2"))),
        rwp!("let-lam-same"; "(let ?v1 ?e (lam ?v1 ?body))" => "(lam ?v1 ?body)"),
        rwp!("let-lam-diff";
            "(let ?v1 ?e (lam ?v2 ?body))" =>
            { CaptureAvoid {
                fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                if_not_free: "(lam ?v2 (let ?v1 ?e ?body))".parse().unwrap(),
                if_free: "(lam ?fresh (let ?v1 ?e (let ?v2 (var ?fresh) ?body)))".parse().unwrap(),
            }}
            if IsNotSameVar::new(var("?v1"), var("?v2"))),
    ]
}

struct CaptureAvoid {
    fresh: Var,
    v2: Var,
    e: Var,
    if_not_free: Pattern<Lambda>,
    if_free: Pattern<Lambda>,
}

impl Applier<Lambda, LambdaAnalysis> for CaptureAvoid {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Lambda>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let e = subst[self.e];
        let v2 = subst[self.v2];
        let v2_free_in_e = egraph[e].data.free.contains(&v2);
        if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = Lambda::Symbol(format!("_{}", eclass).into());
            subst.insert(self.fresh, egraph.add(sym));
            self.if_free
                .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
        } else {
            self.if_not_free
                .apply_one(egraph, eclass, subst, searcher_ast, rule_name)
        }
    }
}

impl ParallelApplier<Lambda, LambdaAnalysis> for CaptureAvoid {
    fn apply_one_par(
        &self,
        manager_channel: &EGraphChannel<Lambda, LambdaAnalysis>,
        eclass: Id,
        subst: &Subst,
        rule_name: Symbol,
    ) {
        let mut manager_channel = manager_channel.clone();
        let e = subst[self.e];
        let v2 = subst[self.v2];
        let v2_free_in_e = manager_channel.egraph[e].data.free.contains(&v2);
        if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = Lambda::Symbol(format!("_{}", eclass).into());
            subst.insert(self.fresh, manager_channel.add(sym));
            manager_channel.flush_additions();
            self.if_free
                .apply_one_par(&manager_channel, eclass, &subst, rule_name)
        } else {
            self.if_not_free
                .apply_one_par(&manager_channel, eclass, subst, rule_name)
        }
    }
}

egg::test_fn_par! {
    lambda_under, rules(),
    "(lam x (+ 4
               (app (lam y (var y))
                    4)))"
    =>
    // "(lam x (+ 4 (let y 4 (var y))))",
    // "(lam x (+ 4 4))",
    "(lam x 8))",
}

egg::test_fn_par! {
    lambda_let_simple, rules(),
    "(let x 0
     (let y 1
     (+ (var x) (var y))))"
    =>
    // "(let ?a 0
    //  (+ (var ?a) 1))",
    // "(+ 0 1)",
    "1",
}

egg::test_fn_par! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_capture, rules(),
    "(let x 1 (lam x (var x)))" => "(lam x 1)"
}

egg::test_fn_par! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_capture_free, rules(),
    "(let y (+ (var x) (var x)) (lam x (var y)))" => "(lam x (+ (var x) (var x)))"
}

egg::test_fn_par! {
    #[should_panic(expected = "Could not prove goal 0")]
    lambda_closure_not_seven, rules(),
    "(let five 5
     (let add-five (lam x (+ (var x) (var five)))
     (let five 6
     (app (var add-five) 1))))"
    =>
    "7"
}

egg::test_fn_par! {
    lambda_compose, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var compose) (var add1)) (var add1))))"
    =>
    "(lam ?x (+ 1
                (app (lam ?y (+ 1 (var ?y)))
                     (var ?x))))",
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn_par! {
    lambda_if_simple, rules(),
    "(if (= 1 1) 7 9)" => "7"
}

egg::test_fn_par! {
    lambda_compose_many, rules(),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var compose) (var add1))
          (app (app (var compose) (var add1))
               (app (app (var compose) (var add1))
                    (app (app (var compose) (var add1))
                         (app (app (var compose) (var add1))
                              (app (app (var compose) (var add1))
                                   (var add1)))))))))"
    =>
    "(lam ?x (+ (var ?x) 7))"
}

egg::test_fn_par! {
    #[cfg(not(debug_assertions))]
    #[cfg_attr(feature = "test-explanations", ignore)]
    lambda_function_repeat, rules(),
    runner = ParallelRunner::default_par()
        .with_time_limit(std::time::Duration::from_secs(20))
        .with_node_limit(150_000)
        .with_iter_limit(60),
    "(let compose (lam f (lam g (lam x (app (var f)
                                       (app (var g) (var x))))))
     (let repeat (fix repeat (lam fun (lam n
        (if (= (var n) 0)
            (lam i (var i))
            (app (app (var compose) (var fun))
                 (app (app (var repeat)
                           (var fun))
                      (+ (var n) -1)))))))
     (let add1 (lam y (+ (var y) 1))
     (app (app (var repeat)
               (var add1))
          2))))"
    =>
    "(lam ?x (+ (var ?x) 2))"
}

egg::test_fn_par! {
    lambda_if, rules(),
    "(let zeroone (lam x
        (if (= (var x) 0)
            0
            1))
        (+ (app (var zeroone) 0)
        (app (var zeroone) 10)))"
    =>
    // "(+ (if false 0 1) (if true 0 1))",
    // "(+ 1 0)",
    "1",
}

egg::test_fn_par! {
    #[cfg(not(debug_assertions))]
    #[cfg_attr(feature = "test-explanations", ignore)]
    lambda_fib, rules(),
    runner = ParallelRunner::default_par()
        .with_iter_limit(60)
        .with_node_limit(500_000),
    "(let fib (fix fib (lam n
        (if (= (var n) 0)
            0
        (if (= (var n) 1)
            1
        (+ (app (var fib)
                (+ (var n) -1))
            (app (var fib)
                (+ (var n) -2)))))))
        (app (var fib) 4))"
    => "3"
}
