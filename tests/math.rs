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

fn random_symbol(rng: &mut impl Rng) -> Symbol {
    let symbol = match rng.gen_range(0..3) {
        0 => "x",
        1 => "y",
        2 => "z",
        _ => "w",
    };

    symbol.parse().unwrap()
}

fn random_expr(size: usize, rng: &mut impl Rng) -> RecExpr<Math> {
    // Symbol or constant
    if size == 1 {
        let mut expr = RecExpr::default();
        if rng.gen_bool(0.5) {
            expr.add(Math::Symbol(random_symbol(rng)));
        } else {
            expr.add(Math::Constant(
                NotNan::new(rng.gen_range(-1.0..1.0)).unwrap(),
            ));
        };

        return expr;
    }

    // Single argument function
    if size == 2 {
        let mut expr = random_expr(1, rng);
        if rng.gen_bool(0.5) {
            expr.add(Math::Sin(0.into()));
        } else {
            expr.add(Math::Cos(0.into()));
        }

        return expr;
    }

    // Single argument function
    if rng.gen_bool(0.1) {
        let mut expr = random_expr(size - 1, rng);
        if rng.gen_bool(0.5) {
            expr.add(Math::Sin((expr.len() - 1).into()));
        } else {
            expr.add(Math::Cos((expr.len() - 1).into()));
        }

        return expr;
    // Integral or derivative
    } else if rng.gen_bool(0.1) {
        let mut expr = random_expr(size - 2, rng);
        expr.add(Math::Symbol(random_symbol(rng)));

        let children = [expr.len() - 2, expr.len() - 1].map(|id| id.into());

        if rng.gen_bool(0.5) {
            expr.add(Math::Integral(children));
        } else {
            expr.add(Math::Diff(children));
        }
        return expr;
    // Two argument function
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
pub fn rules() -> Vec<egg::Rewrite<Math, ConstantFold>> { vec![
    // rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    // rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    // rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    // rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
    //
    // rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    // rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))" if IsNotZero::new("?b")),
    rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    rw!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if IsNotZero::new("?b")),

    rw!("zero-add"; "(+ ?a 0)" => "?a"),
    rw!("zero-mul"; "(* ?a 0)" => "0"),
    rw!("one-mul";  "(* ?a 1)" => "?a"),

    // rw!("add-zero"; "?a" => "(+ ?a 0)"),
    // rw!("mul-one";  "?a" => "(* ?a 1)"),

    rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    rw!("cancel-div"; "(/ ?a ?a)" => "1" if IsNotZero::new("?a")),

    // rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
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
    //  rwp!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    //  rwp!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    //  rwp!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    //  rwp!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
    //
    // rwp!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    // rwp!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))" if IsNotZero::new("?b")),
    rwp!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    rwp!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if IsNotZero::new("?b")),

    rwp!("zero-add"; "(+ ?a 0)" => "?a"),
    rwp!("zero-mul"; "(* ?a 0)" => "0"),
    rwp!("one-mul";  "(* ?a 1)" => "?a"),

    // rwp!("add-zero"; "?a" => "(+ ?a 0)"),
    // rwp!("mul-one";  "?a" => "(* ?a 1)"),

    rwp!("cancel-sub"; "(- ?a ?a)" => "0"),
    rwp!("cancel-div"; "(/ ?a ?a)" => "1" if IsNotZero::new("?a")),

    // rwp!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
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
fn random_exprs() {
    let mut rng = ChaCha8Rng::seed_from_u64(1);
    let expr = random_expr(10000, &mut rng);
    println!("{}", expr.len());
    println!("{}", expr.pretty(100));
}

#[test]
fn parallel_bench() {
    let mut exprs = Vec::new();
    for length in [
        10, 100, 1000, 10_000, /*100_000, 1_000_000,*/
    ] {
        for seed in 0..3 {
            let mut rng = ChaCha8Rng::seed_from_u64(seed);
            let expr = random_expr(length, &mut rng);
            exprs.push(expr);
        }
    }

    let mut log = String::from(test::csv_header());

    log += &crate::test::parallel_bench(
        &rules_par(),
        &rules(),
        &exprs,
        &[
            1, 2, 3, 4, /*5,*/ 6, /*7,*/ 8, //10, 12, 14, 16, 20, 24, 28, 32,
        ],
        "test.csv",
    );
}

#[test]
fn parallel_mem() {
    let length: usize = std::env::var("PE_LEN").unwrap().parse().unwrap();
    let seed: u64 = std::env::var("PE_SEED").unwrap().parse().unwrap();
    let seq: bool = std::env::var("PE_SEQ").unwrap().parse().unwrap();
    println!("Memory test");
    println!("Len: {length}, seed: {seed}, seq: {seq}");

    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let expr = random_expr(length, &mut rng);

    if seq {
        crate::test::parallel_bench_peak_mem(&rules_par(), &expr);
    } else {
        crate::test::parallel_bench_peak_mem_sing(&rules(), &expr);
    }
}
