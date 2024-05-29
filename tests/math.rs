use egg::{rewrite as rw, rewrite_par as rwp, *};
use ordered_float::NotNan;
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;

pub type EGraph = egg::EGraph<Math, ConstantFold>;
pub type Rewrite = egg::Rewrite<Math, ConstantFold>;

pub type Constant = NotNan<f64>;

define_language! {
    pub enum Math {
        "d" = Diff([Id; 2]),
        "i" = Integral([Id; 2]),

        "+" =   Add([Id; 2]),
        "-" =   Sub([Id; 2]),
        "*" =   Mul([Id; 2]),
        "/" =   Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "ln" = Ln(Id),
        "sqrt" = Sqrt(Id),

        "sin" = Sin(Id),
        "cos" = Cos(Id),

        Constant(Constant),
        Symbol(Symbol),
    }
}

fn random_expr(size: usize, rng: &mut impl Rng) -> RecExpr<Math> {
    if size == 1 {
        let mut expr = RecExpr::default();
        if rng.gen_bool(0.5) {
            let symbol = match rng.gen_range(0..3) {
                0 => "x",
                1 => "y",
                2 => "z",
                _ => "w",
            };

            expr.add(Math::Symbol(symbol.parse().unwrap()));
        } else {
            expr.add(Math::Constant(
                NotNan::new(rng.gen_range(-1.0..1.0)).unwrap(),
            ));
        };

        return expr;
    }

    if size == 2 {
        let mut expr = random_expr(1, rng);
        if rng.gen_bool(0.5) {
            expr.add(Math::Sin(0.into()));
        } else {
            expr.add(Math::Cos(0.into()));
        }
        
        return expr;
    }

    if rng.gen_bool(0.1) {
        let mut expr = random_expr(size - 1, rng);
        if rng.gen_bool(0.5) {
            expr.add(Math::Sin((expr.len() - 1).into()));
        } else {
            expr.add(Math::Cos((expr.len() - 1).into()));
        }

        return expr;
    } else {
        let left_size = (size - 1) / 2;
        let right_size = size - 1 - left_size;

        let left = random_expr(left_size, rng);
        let right = random_expr(right_size, rng);
        let mut unified = left.concat(&right);

        let left_id = Id::from(left_size - 1);
        let right_id = Id::from(unified.len() - 1);

        let to_add = match rng.gen_range(0..5) {
            0 => Math::Add([left_id, right_id]),
            1 => Math::Sub([left_id, right_id]),
            2 => Math::Mul([left_id, right_id]),
            3 => Math::Div([left_id, right_id]),
            _ => Math::Pow([left_id, right_id]),
        };

        unified.add(to_add);

        return unified;
    }
}

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator
pub struct MathCostFn;
impl egg::CostFunction<Math> for MathCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Math, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            Math::Diff(..) => 100,
            Math::Integral(..) => 100,
            _ => 1,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

#[derive(Default)]
pub struct ConstantFold;
impl Analysis<Math> for ConstantFold {
    type Data = Option<(Constant, PatternAst<Math>)>;

    fn make(egraph: &EGraph, enode: &Math) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            Math::Constant(c) => (*c, format!("{}", c).parse().unwrap()),
            Math::Add([a, b]) => (
                x(a)? + x(b)?,
                format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Math::Sub([a, b]) => (
                x(a)? - x(b)?,
                format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Math::Mul([a, b]) => (
                x(a)? * x(b)?,
                format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Math::Div([a, b]) if x(b) != Some(NotNan::new(0.0).unwrap()) => (
                x(a)? / x(b)?,
                format!("(/ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let data = egraph[id].data.clone();
        if let Some((c, pat)) = data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(Math::Constant(c));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

struct IsConstOrDistinctVar {
    v: Var,
    w: Var,
}

impl IsConstOrDistinctVar {
    pub fn new(v: &str, w: &str) -> Self {
        Self {
            v: v.parse().unwrap(),
            w: w.parse().unwrap(),
        }
    }
}

impl Condition<Math, ConstantFold> for IsConstOrDistinctVar {
    fn check(
        &self,
        egraph: &mut egg::EGraph<Math, ConstantFold>,
        eclass: Id,
        subst: &Subst,
    ) -> bool {
        self.check_const(egraph, eclass, subst)
    }
}

impl ConstCondition<Math, ConstantFold> for IsConstOrDistinctVar {
    fn check_const(
        &self,
        egraph: &egg::EGraph<Math, ConstantFold>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        egraph.find(subst[self.v]) != egraph.find(subst[self.w])
            && (egraph[subst[self.v]].data.is_some()
                || egraph[subst[self.v]]
                    .nodes
                    .iter()
                    .any(|n| matches!(n, Math::Symbol(..))))
    }
}

struct IsConst {
    var: Var,
}

impl IsConst {
    pub fn new(var: &str) -> Self {
        Self {
            var: var.parse().unwrap(),
        }
    }
}

impl Condition<Math, ConstantFold> for IsConst {
    fn check(
        &self,
        egraph: &mut egg::EGraph<Math, ConstantFold>,
        eclass: Id,
        subst: &Subst,
    ) -> bool {
        self.check_const(egraph, eclass, subst)
    }
}

impl ConstCondition<Math, ConstantFold> for IsConst {
    fn check_const(
        &self,
        egraph: &egg::EGraph<Math, ConstantFold>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        egraph[subst[self.var]].data.is_some()
    }
}

struct IsSym {
    var: Var,
}

impl IsSym {
    pub fn new(var: &str) -> Self {
        Self {
            var: var.parse().unwrap(),
        }
    }
}

impl Condition<Math, ConstantFold> for IsSym {
    fn check(
        &self,
        egraph: &mut egg::EGraph<Math, ConstantFold>,
        eclass: Id,
        subst: &Subst,
    ) -> bool {
        self.check_const(egraph, eclass, subst)
    }
}

impl ConstCondition<Math, ConstantFold> for IsSym {
    fn check_const(
        &self,
        egraph: &egg::EGraph<Math, ConstantFold>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        egraph[subst[self.var]]
            .nodes
            .iter()
            .any(|n| matches!(n, Math::Symbol(..)))
    }
}

struct IsNotZero {
    var: Var,
}

impl IsNotZero {
    pub fn new(var: &str) -> Self {
        Self {
            var: var.parse().unwrap(),
        }
    }
}

impl Condition<Math, ConstantFold> for IsNotZero {
    fn check(
        &self,
        egraph: &mut egg::EGraph<Math, ConstantFold>,
        eclass: Id,
        subst: &Subst,
    ) -> bool {
        self.check_const(egraph, eclass, subst)
    }
}

impl ConstCondition<Math, ConstantFold> for IsNotZero {
    fn check_const(
        &self,
        egraph: &egg::EGraph<Math, ConstantFold>,
        _eclass: Id,
        subst: &Subst,
    ) -> bool {
        if let Some(n) = &egraph[subst[self.var]].data {
            *(n.0) != 0.0
        } else {
            true
        }
    }
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> { vec![
    rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

    rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))" if IsNotZero::new("?b")),
    // rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    // rw!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

    rw!("zero-add"; "(+ ?a 0)" => "?a"),
    rw!("zero-mul"; "(* ?a 0)" => "0"),
    rw!("one-mul";  "(* ?a 1)" => "?a"),

    rw!("add-zero"; "?a" => "(+ ?a 0)"),
    rw!("mul-one";  "?a" => "(* ?a 1)"),

    rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    rw!("cancel-div"; "(/ ?a ?a)" => "1" if IsNotZero::new("?a")),

    rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

    rw!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
    rw!("pow0"; "(pow ?x 0)" => "1"
        if IsNotZero::new("?x")),
    rw!("pow1"; "(pow ?x 1)" => "?x"),
    rw!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
    rw!("pow-recip"; "(pow ?x -1)" => "(/ 1 ?x)"
        if IsNotZero::new("?x")),
    rw!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1" if IsNotZero::new("?x")),

    rw!("d-variable"; "(d ?x ?x)" => "1" if IsSym::new("?x")),
    rw!("d-constant"; "(d ?x ?c)" => "0" if IsSym::new("?x") if IsConstOrDistinctVar::new("?c", "?x")),

    rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
    rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

    rw!("d-sin"; "(d ?x (sin ?x))" => "(cos ?x)"),
    rw!("d-cos"; "(d ?x (cos ?x))" => "(* -1 (sin ?x))"),

    rw!("d-ln"; "(d ?x (ln ?x))" => "(/ 1 ?x)" if IsNotZero::new("?x")),

    rw!("d-power";
        "(d ?x (pow ?f ?g))" =>
        "(* (pow ?f ?g)
            (+ (* (d ?x ?f)
                  (/ ?g ?f))
               (* (d ?x ?g)
                  (ln ?f))))"
        if IsNotZero::new("?f")
        if IsNotZero::new("?g")
    ),

    rw!("i-one"; "(i 1 ?x)" => "?x"),
    rw!("i-power-const"; "(i (pow ?x ?c) ?x)" =>
        "(/ (pow ?x (+ ?c 1)) (+ ?c 1))" if IsConst::new("?c")),
    rw!("i-cos"; "(i (cos ?x) ?x)" => "(sin ?x)"),
    rw!("i-sin"; "(i (sin ?x) ?x)" => "(* -1 (cos ?x))"),
    rw!("i-sum"; "(i (+ ?f ?g) ?x)" => "(+ (i ?f ?x) (i ?g ?x))"),
    rw!("i-dif"; "(i (- ?f ?g) ?x)" => "(- (i ?f ?x) (i ?g ?x))"),
    rw!("i-parts"; "(i (* ?a ?b) ?x)" =>
        "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))"),
]}

#[rustfmt::skip]
pub fn rules_par() -> Vec<ParallelRewrite<Math, ConstantFold>> { vec![
    rwp!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    rwp!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    rwp!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rwp!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

    rwp!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rwp!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))" if IsNotZero::new("?b")),
    // rwp!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    // rwp!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

    rwp!("zero-add"; "(+ ?a 0)" => "?a"),
    rwp!("zero-mul"; "(* ?a 0)" => "0"),
    rwp!("one-mul";  "(* ?a 1)" => "?a"),

    rwp!("add-zero"; "?a" => "(+ ?a 0)"),
    rwp!("mul-one";  "?a" => "(* ?a 1)"),

    rwp!("cancel-sub"; "(- ?a ?a)" => "0"),
    rwp!("cancel-div"; "(/ ?a ?a)" => "1" if IsNotZero::new("?a")),

    rwp!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
    rwp!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

    rwp!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
    rwp!("pow0"; "(pow ?x 0)" => "1"
        if IsNotZero::new("?x")),
    rwp!("pow1"; "(pow ?x 1)" => "?x"),
    rwp!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
    rwp!("pow-recip"; "(pow ?x -1)" => "(/ 1 ?x)"
        if IsNotZero::new("?x")),
    rwp!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1" if IsNotZero::new("?x")),

    rwp!("d-variable"; "(d ?x ?x)" => "1" if IsSym::new("?x")),
    rwp!("d-constant"; "(d ?x ?c)" => "0" if IsSym::new("?x") if IsConstOrDistinctVar::new("?c", "?x")),

    rwp!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
    rwp!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

    rwp!("d-sin"; "(d ?x (sin ?x))" => "(cos ?x)"),
    rwp!("d-cos"; "(d ?x (cos ?x))" => "(* -1 (sin ?x))"),

    rwp!("d-ln"; "(d ?x (ln ?x))" => "(/ 1 ?x)" if IsNotZero::new("?x")),

    rwp!("d-power";
        "(d ?x (pow ?f ?g))" =>
        "(* (pow ?f ?g)
            (+ (* (d ?x ?f)
                  (/ ?g ?f))
               (* (d ?x ?g)
                  (ln ?f))))"
        if IsNotZero::new("?f")
        if IsNotZero::new("?g")
    ),

    rwp!("i-one"; "(i 1 ?x)" => "?x"),
    rwp!("i-power-const"; "(i (pow ?x ?c) ?x)" =>
        "(/ (pow ?x (+ ?c 1)) (+ ?c 1))" if IsConst::new("?c")),
    rwp!("i-cos"; "(i (cos ?x) ?x)" => "(sin ?x)"),
    rwp!("i-sin"; "(i (sin ?x) ?x)" => "(* -1 (cos ?x))"),
    rwp!("i-sum"; "(i (+ ?f ?g) ?x)" => "(+ (i ?f ?x) (i ?g ?x))"),
    rwp!("i-dif"; "(i (- ?f ?g) ?x)" => "(- (i ?f ?x) (i ?g ?x))"),
    rwp!("i-parts"; "(i (* ?a ?b) ?x)" =>
        "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))"),
]}

egg::test_fn! {
    math_associate_adds, [
        rw!("comm-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    ],
    runner = Runner::default()
        .with_iter_limit(7)
        .with_scheduler(SimpleScheduler),
    "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))"
    =>
    "(+ 7 (+ 6 (+ 5 (+ 4 (+ 3 (+ 2 1))))))"
    @check |r: Runner<Math, ()>| assert_eq!(r.egraph.number_of_classes(), 127)
}

egg::test_fn_par! {
    #[should_panic(expected = "Could not prove goal 0")]
    math_fail, rules_par(),
    "(+ x y)" => "(/ x y)"
}

egg::test_fn_par! {math_simplify_add, rules_par(), "(+ x (+ x (+ x x)))" => "(* 4 x)" }
egg::test_fn_par! {math_powers, rules_par(), "(* (pow 2 x) (pow 2 y))" => "(pow 2 (+ x y))"}

egg::test_fn_par! {
    math_simplify_const, rules_par(),
    "(+ 1 (- a (* (- 2 1) a)))" => "1"
}

egg::test_fn_par! {
    math_simplify_root, rules_par(),
    runner = ParallelRunner::default_par().with_node_limit(75_000),
    r#"
    (/ 1
       (- (/ (+ 1 (sqrt five))
             2)
          (/ (- 1 (sqrt five))
             2)))"#
    =>
    "(/ 1 (sqrt five))"
}

egg::test_fn_par! {
    math_simplify_factor, rules_par(),
    "(* (+ x 3) (+ x 1))"
    =>
    "(+ (+ (* x x) (* 4 x)) 3)"
}

egg::test_fn_par! {math_diff_same,      rules_par(), "(d x x)" => "1"}
egg::test_fn_par! {math_diff_different, rules_par(), "(d x y)" => "0"}
egg::test_fn_par! {math_diff_simple1,   rules_par(), "(d x (+ 1 (* 2 x)))" => "2"}
egg::test_fn_par! {math_diff_simple2,   rules_par(), "(d x (+ 1 (* y x)))" => "y"}
egg::test_fn_par! {math_diff_ln,        rules_par(), "(d x (ln x))" => "(/ 1 x)"}

egg::test_fn_par! {
    diff_power_simple, rules_par(),
    "(d x (pow x 3))" => "(* 3 (pow x 2))"
}

egg::test_fn_par! {
    diff_power_harder, rules_par(),
    runner = ParallelRunner::default_par()
        .with_time_limit(std::time::Duration::from_secs(10))
        .with_iter_limit(60)
        .with_node_limit(100_000)
        // HACK this needs to "see" the end expression
        .with_expr(&"(* x (- (* 3 x) 14))".parse().unwrap()),
    "(d x (- (pow x 3) (* 7 (pow x 2))))"
    =>
    "(* x (- (* 3 x) 14))"
}

egg::test_fn_par! {
    integ_one, rules_par(), "(i 1 x)" => "x"
}

egg::test_fn_par! {
    integ_sin, rules_par(), "(i (cos x) x)" => "(sin x)"
}

egg::test_fn_par! {
    integ_x, rules_par(), "(i (pow x 1) x)" => "(/ (pow x 2) 2)"
}

egg::test_fn_par! {
    integ_part1, rules_par(), "(i (* x (cos x)) x)" => "(+ (* x (sin x)) (cos x))"
}

egg::test_fn_par! {
    integ_part2, rules_par(),
    "(i (* (cos x) x) x)" => "(+ (* x (sin x)) (cos x))"
}

egg::test_fn_par! {
    integ_part3, rules_par(), "(i (ln x) x)" => "(- (* x (ln x)) x)"
}

#[test]
fn assoc_mul_saturates() {
    let expr: RecExpr<Math> = "(* x 1)".parse().unwrap();

    let runner: Runner<Math, ConstantFold> = Runner::default()
        .with_iter_limit(3)
        .with_expr(&expr)
        .run(&rules());

    assert!(matches!(runner.stop_reason, Some(StopReason::Saturated)));
}

#[test]
fn test_union_trusted() {
    let expr: RecExpr<Math> = "(+ (* x 1) y)".parse().unwrap();
    let expr2 = "20".parse().unwrap();
    let mut runner: Runner<Math, ConstantFold> = Runner::default()
        .with_explanations_enabled()
        .with_iter_limit(3)
        .with_expr(&expr)
        .run(&rules());
    let lhs = runner.egraph.add_expr(&expr);
    let rhs = runner.egraph.add_expr(&expr2);
    runner.egraph.union_trusted(lhs, rhs, "whatever");
    let proof = runner.explain_equivalence(&expr, &expr2).get_flat_strings();
    assert_eq!(proof, vec!["(+ (* x 1) y)", "(Rewrite=> whatever 20)"]);
}

#[cfg(feature = "lp")]
#[test]
fn math_lp_extract() {
    let expr: RecExpr<Math> = "(pow (+ x (+ x x)) (+ x x))".parse().unwrap();

    let runner: Runner<Math, ConstantFold> = Runner::default()
        .with_iter_limit(3)
        .with_expr(&expr)
        .run(&rules());
    let root = runner.roots[0];

    let best = Extractor::new(&runner.egraph, AstSize).find_best(root).1;
    let lp_best = LpExtractor::new(&runner.egraph, AstSize).solve(root);

    println!("input   [{}] {}", expr.as_ref().len(), expr);
    println!("normal  [{}] {}", best.as_ref().len(), best);
    println!("ilp cse [{}] {}", lp_best.as_ref().len(), lp_best);

    assert_ne!(best, lp_best);
    assert_eq!(lp_best.as_ref().len(), 4);
}

#[test]
fn math_ematching_bench() {
    let exprs = &[
        "(i (ln x) x)",
        "(i (+ x (cos x)) x)",
        "(i (* (cos x) x) x)",
        "(d x (+ 1 (* 2 x)))",
        "(d x (- (pow x 3) (* 7 (pow x 2))))",
        "(+ (* y (+ x y)) (- (+ x 2) (+ x x)))",
        "(/ 1 (- (/ (+ 1 (sqrt five)) 2) (/ (- 1 (sqrt five)) 2)))",
    ];

    let extra_patterns = &[
        "(+ ?a (+ ?b ?c))",
        "(+ (+ ?a ?b) ?c)",
        "(* ?a (* ?b ?c))",
        "(* (* ?a ?b) ?c)",
        "(+ ?a (* -1 ?b))",
        "(* ?a (pow ?b -1))",
        "(* ?a (+ ?b ?c))",
        "(pow ?a (+ ?b ?c))",
        "(+ (* ?a ?b) (* ?a ?c))",
        "(* (pow ?a ?b) (pow ?a ?c))",
        "(* ?x (/ 1 ?x))",
        "(d ?x (+ ?a ?b))",
        "(+ (d ?x ?a) (d ?x ?b))",
        "(d ?x (* ?a ?b))",
        "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))",
        "(d ?x (sin ?x))",
        "(d ?x (cos ?x))",
        "(* -1 (sin ?x))",
        "(* -1 (cos ?x))",
        "(i (cos ?x) ?x)",
        "(i (sin ?x) ?x)",
        "(d ?x (ln ?x))",
        "(d ?x (pow ?f ?g))",
        "(* (pow ?f ?g) (+ (* (d ?x ?f) (/ ?g ?f)) (* (d ?x ?g) (ln ?f))))",
        "(i (pow ?x ?c) ?x)",
        "(/ (pow ?x (+ ?c 1)) (+ ?c 1))",
        "(i (+ ?f ?g) ?x)",
        "(i (- ?f ?g) ?x)",
        "(+ (i ?f ?x) (i ?g ?x))",
        "(- (i ?f ?x) (i ?g ?x))",
        "(i (* ?a ?b) ?x)",
        "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))",
    ];

    egg::test::bench_egraph("math", rules(), exprs, extra_patterns);
}

#[test]
fn test_basic_egraph_union_intersect() {
    let mut egraph1 = EGraph::new(ConstantFold {}).with_explanations_enabled();
    let mut egraph2 = EGraph::new(ConstantFold {}).with_explanations_enabled();
    egraph1.union_instantiations(
        &"x".parse().unwrap(),
        &"y".parse().unwrap(),
        &Default::default(),
        "",
    );
    egraph1.union_instantiations(
        &"y".parse().unwrap(),
        &"z".parse().unwrap(),
        &Default::default(),
        "",
    );
    egraph2.union_instantiations(
        &"x".parse().unwrap(),
        &"y".parse().unwrap(),
        &Default::default(),
        "",
    );
    egraph2.union_instantiations(
        &"x".parse().unwrap(),
        &"a".parse().unwrap(),
        &Default::default(),
        "",
    );

    let mut egraph3 = egraph1.egraph_intersect(&egraph2, ConstantFold {});

    egraph2.egraph_union(&egraph1);

    assert_eq!(
        egraph2.add_expr(&"x".parse().unwrap()),
        egraph2.add_expr(&"y".parse().unwrap())
    );
    assert_eq!(
        egraph3.add_expr(&"x".parse().unwrap()),
        egraph3.add_expr(&"y".parse().unwrap())
    );

    assert_eq!(
        egraph2.add_expr(&"x".parse().unwrap()),
        egraph2.add_expr(&"z".parse().unwrap())
    );
    assert_ne!(
        egraph3.add_expr(&"x".parse().unwrap()),
        egraph3.add_expr(&"z".parse().unwrap())
    );
    assert_eq!(
        egraph2.add_expr(&"x".parse().unwrap()),
        egraph2.add_expr(&"a".parse().unwrap())
    );
    assert_ne!(
        egraph3.add_expr(&"x".parse().unwrap()),
        egraph3.add_expr(&"a".parse().unwrap())
    );

    assert_eq!(
        egraph2.add_expr(&"y".parse().unwrap()),
        egraph2.add_expr(&"a".parse().unwrap())
    );
    assert_ne!(
        egraph3.add_expr(&"y".parse().unwrap()),
        egraph3.add_expr(&"a".parse().unwrap())
    );
}

#[test]
fn test_intersect_basic() {
    let mut egraph1 = EGraph::new(ConstantFold {}).with_explanations_enabled();
    let mut egraph2 = EGraph::new(ConstantFold {}).with_explanations_enabled();
    egraph1.union_instantiations(
        &"(+ x 0)".parse().unwrap(),
        &"(+ y 0)".parse().unwrap(),
        &Default::default(),
        "",
    );
    egraph2.union_instantiations(
        &"x".parse().unwrap(),
        &"y".parse().unwrap(),
        &Default::default(),
        "",
    );
    egraph2.add_expr(&"(+ x 0)".parse().unwrap());
    egraph2.add_expr(&"(+ y 0)".parse().unwrap());

    let mut egraph3 = egraph1.egraph_intersect(&egraph2, ConstantFold {});

    assert_ne!(
        egraph3.add_expr(&"x".parse().unwrap()),
        egraph3.add_expr(&"y".parse().unwrap())
    );
    assert_eq!(
        egraph3.add_expr(&"(+ x 0)".parse().unwrap()),
        egraph3.add_expr(&"(+ y 0)".parse().unwrap())
    );
}

#[test]
fn test_medium_intersect() {
    let mut egraph1 = egg::EGraph::<Math, ()>::new(());

    egraph1.add_expr(&"(sqrt (ln 1))".parse().unwrap());
    let ln = egraph1.add_expr(&"(ln 1)".parse().unwrap());
    let a = egraph1.add_expr(&"(sqrt (sin pi))".parse().unwrap());
    let b = egraph1.add_expr(&"(* 1 pi)".parse().unwrap());
    let pi = egraph1.add_expr(&"pi".parse().unwrap());
    egraph1.union(a, b);
    egraph1.union(a, pi);
    let c = egraph1.add_expr(&"(+ pi pi)".parse().unwrap());
    egraph1.union(ln, c);
    let k = egraph1.add_expr(&"k".parse().unwrap());
    let one = egraph1.add_expr(&"1".parse().unwrap());
    egraph1.union(k, one);
    egraph1.rebuild();

    assert_eq!(
        egraph1.add_expr(&"(ln k)".parse().unwrap()),
        egraph1.add_expr(&"(+ (* k pi) (* k pi))".parse().unwrap())
    );

    let mut egraph2 = egg::EGraph::<Math, ()>::new(());
    let ln = egraph2.add_expr(&"(ln 2)".parse().unwrap());
    let k = egraph2.add_expr(&"k".parse().unwrap());
    let mk1 = egraph2.add_expr(&"(* k 1)".parse().unwrap());
    egraph2.union(mk1, k);
    let two = egraph2.add_expr(&"2".parse().unwrap());
    egraph2.union(mk1, two);
    let mul2pi = egraph2.add_expr(&"(+ (* 2 pi) (* 2 pi))".parse().unwrap());
    egraph2.union(ln, mul2pi);
    egraph2.rebuild();

    assert_eq!(
        egraph2.add_expr(&"(ln k)".parse().unwrap()),
        egraph2.add_expr(&"(+ (* k pi) (* k pi))".parse().unwrap())
    );

    let mut egraph3 = egraph1.egraph_intersect(&egraph2, ());

    assert_eq!(
        egraph3.add_expr(&"(ln k)".parse().unwrap()),
        egraph3.add_expr(&"(+ (* k pi) (* k pi))".parse().unwrap())
    );
}

#[test]
fn random_exprs() {
    let mut rng = ChaCha8Rng::seed_from_u64(1);
    let expr = random_expr(10000, &mut rng);
    println!("{}", expr.len());
    println!("{}", expr.pretty(100));
}
