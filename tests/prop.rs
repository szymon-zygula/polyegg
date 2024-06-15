use rand::prelude::*;
use rand_chacha::ChaCha8Rng;

use egg::*;

define_language! {
    enum Prop {
        Bool(bool),
        "&" = And([Id; 2]),
        "~" = Not(Id),
        "|" = Or([Id; 2]),
        "->" = Implies([Id; 2]),
        Symbol(Symbol),
    }
}

fn random_symbol(rng: &mut impl Rng) -> Symbol {
    let symbol = match rng.gen_range(0..3) {
        0 => "p",
        1 => "q",
        2 => "r",
        _ => "s",
    };

    symbol.parse().unwrap()
}

fn random_expr(size: usize, rng: &mut impl Rng) -> RecExpr<Prop> {
    // Symbol or constant
    if size == 1 {
        let mut expr = RecExpr::default();
        if rng.gen_bool(0.5) {
            expr.add(Prop::Symbol(random_symbol(rng)));
        } else {
            expr.add(Prop::Bool(rng.gen_bool(0.5)));
        };

        return expr;
    }

    // Negation
    if size == 2 || rng.gen_bool(0.2) {
        let mut expr = random_expr(size - 1, rng);
        expr.add(Prop::Not((expr.len() - 1).into()));
        return expr;
    }

    // Split the tree
    let left_size = (size - 1) / 2;
    let right_size = size - 1 - left_size;

    let left = random_expr(left_size, rng);
    let right = random_expr(right_size, rng);
    let mut unified = left.concat(&right);

    let left_id = Id::from(left_size - 1);
    let right_id = Id::from(unified.len() - 1);

    let to_add = match rng.gen_range(0..3) {
        0 => Prop::And([left_id, right_id]),
        1 => Prop::Or([left_id, right_id]),
        _ => Prop::Implies([left_id, right_id]),
    };

    unified.add(to_add);

    unified
}

type EGraph = egg::EGraph<Prop, ConstantFold>;
type Rewrite = egg::ParallelRewrite<Prop, ConstantFold>;

#[derive(Default)]
struct ConstantFold;
impl Analysis<Prop> for ConstantFold {
    type Data = Option<(bool, PatternAst<Prop>)>;
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn make(egraph: &EGraph, enode: &Prop) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|c| c.0);
        let result = match enode {
            Prop::Bool(c) => Some((*c, c.to_string().parse().unwrap())),
            Prop::Symbol(_) => None,
            Prop::And([a, b]) => Some((
                x(a)? && x(b)?,
                format!("(& {} {})", x(a)?, x(b)?).parse().unwrap(),
            )),
            Prop::Not(a) => Some((!x(a)?, format!("(~ {})", x(a)?).parse().unwrap())),
            Prop::Or([a, b]) => Some((
                x(a)? || x(b)?,
                format!("(| {} {})", x(a)?, x(b)?).parse().unwrap(),
            )),
            Prop::Implies([a, b]) => Some((
                !x(a)? || x(b)?,
                format!("(-> {} {})", x(a)?, x(b)?).parse().unwrap(),
            )),
        };
        // println!("Make: {:?} -> {:?}", enode, result);
        result
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.clone() {
            egraph.union_instantiations(
                &c.1,
                &c.0.to_string().parse().unwrap(),
                &Default::default(),
                "analysis".to_string(),
            );
        }
    }
}

macro_rules! rule_par {
    ($name:ident, $left:literal, $right:literal) => {
        #[allow(dead_code)]
        fn $name() -> Rewrite {
            rewrite_par!(stringify!($name); $left => $right)
        }
    };
    ($name:ident, $name2:ident, $left:literal, $right:literal) => {
        rule_par!($name, $left, $right);
        rule_par!($name2, $right, $left);
    };
}

rule_par! {def_imply_par, def_imply_flip_par,   "(-> ?a ?b)",       "(| (~ ?a) ?b)"          }
rule_par! {double_neg_par, double_neg_flip_par,  "(~ (~ ?a))",       "?a"                     }
rule_par! {assoc_or_par,    "(| ?a (| ?b ?c))", "(| (| ?a ?b) ?c)"       }
rule_par! {dist_and_or_par, "(& ?a (| ?b ?c))", "(| (& ?a ?b) (& ?a ?c))"}
rule_par! {dist_or_and_par, "(| ?a (& ?b ?c))", "(& (| ?a ?b) (| ?a ?c))"}
rule_par! {comm_or_par,     "(| ?a ?b)",        "(| ?b ?a)"              }
rule_par! {comm_and_par,    "(& ?a ?b)",        "(& ?b ?a)"              }
rule_par! {lem_par,         "(| ?a (~ ?a))",    "true"                      }
rule_par! {or_true_par,     "(| ?a true)",         "true"                      }
rule_par! {and_true_par,    "(& ?a true)",         "?a"                     }
rule_par! {contrapositive_par, "(-> ?a ?b)",    "(-> (~ ?b) (~ ?a))"     }

macro_rules! rule {
    ($name:ident, $left:literal, $right:literal) => {
        #[allow(dead_code)]
        fn $name() -> egg::Rewrite<Prop, ConstantFold> {
            rewrite!(stringify!($name); $left => $right)
        }
    };
    ($name:ident, $name2:ident, $left:literal, $right:literal) => {
        rule!($name, $left, $right);
        rule!($name2, $right, $left);
    };
}

rule! {def_imply, def_imply_flip,   "(-> ?a ?b)",       "(| (~ ?a) ?b)"          }
rule! {double_neg, double_neg_flip,  "(~ (~ ?a))",       "?a"                     }
rule! {assoc_or,    "(| ?a (| ?b ?c))", "(| (| ?a ?b) ?c)"       }
rule! {dist_and_or, "(& ?a (| ?b ?c))", "(| (& ?a ?b) (& ?a ?c))"}
rule! {dist_or_and, "(| ?a (& ?b ?c))", "(& (| ?a ?b) (| ?a ?c))"}
rule! {comm_or,     "(| ?a ?b)",        "(| ?b ?a)"              }
rule! {comm_and,    "(& ?a ?b)",        "(& ?b ?a)"              }
rule! {lem,         "(| ?a (~ ?a))",    "true"                      }
rule! {or_true,     "(| ?a true)",         "true"                      }
rule! {and_true,    "(& ?a true)",         "?a"                     }
rule! {contrapositive, "(-> ?a ?b)",    "(-> (~ ?b) (~ ?a))"     }

// this has to be a multipattern since (& (-> ?a ?b) (-> (~ ?a) ?c))  !=  (| ?b ?c)
// see https://github.com/egraphs-good/egg/issues/185
fn lem_imply_par() -> Rewrite {
    multi_rewrite_par!(
        "lem_imply";
        "?value = true = (& (-> ?a ?b) (-> (~ ?a) ?c))"
        =>
        "?value = (| ?b ?c)"
    )
}

fn lem_imply() -> egg::Rewrite<Prop, ConstantFold> {
    multi_rewrite!(
        "lem_imply";
        "?value = true = (& (-> ?a ?b) (-> (~ ?a) ?c))"
        =>
        "?value = (| ?b ?c)"
    )
}

fn prove_something(name: &str, start: &str, rewrites: &[Rewrite], goals: &[&str]) {
    let _ = env_logger::builder().is_test(true).try_init();
    println!("Proving {}", name);

    let start_expr: RecExpr<_> = start.parse().unwrap();
    let goal_exprs: Vec<RecExpr<_>> = goals.iter().map(|g| g.parse().unwrap()).collect();

    let mut runner = ParallelRunner::default_par()
        .with_iter_limit(20)
        .with_node_limit(5_000)
        .with_expr(&start_expr);

    // we are assume the input expr is true
    // this is needed for the soundness of lem_imply
    let true_id = runner.egraph.add(Prop::Bool(true));
    let root = runner.roots[0];
    runner.egraph.union(root, true_id);
    runner.egraph.rebuild();

    let egraph = runner.run_par(rewrites).egraph;

    for (i, (goal_expr, goal_str)) in goal_exprs.iter().zip(goals).enumerate() {
        println!("Trying to prove goal {}: {}", i, goal_str);
        let equivs = egraph.equivs(&start_expr, goal_expr);
        if equivs.is_empty() {
            panic!("Couldn't prove goal {}: {}", i, goal_str);
        }
    }
}

#[test]
fn prove_contrapositive() {
    let _ = env_logger::builder().is_test(true).try_init();
    let rules = &[
        def_imply_par(),
        def_imply_flip_par(),
        double_neg_flip_par(),
        comm_or_par(),
    ];
    prove_something(
        "contrapositive",
        "(-> x y)",
        rules,
        &[
            "(-> x y)",
            "(| (~ x) y)",
            "(| (~ x) (~ (~ y)))",
            "(| (~ (~ y)) (~ x))",
            "(-> (~ y) (~ x))",
        ],
    );
}

#[test]
fn prove_chain() {
    let _ = env_logger::builder().is_test(true).try_init();
    let rules = &[
        // rules needed for contrapositive
        def_imply_par(),
        def_imply_flip_par(),
        double_neg_flip_par(),
        comm_or_par(),
        // and some others
        comm_and_par(),
        lem_imply_par(),
    ];
    prove_something(
        "chain",
        "(& (-> x y) (-> y z))",
        rules,
        &[
            "(& (-> x y) (-> y z))",
            "(& (-> (~ y) (~ x)) (-> y z))",
            "(& (-> y z)         (-> (~ y) (~ x)))",
            "(| z (~ x))",
            "(| (~ x) z)",
            "(-> x z)",
        ],
    );
}

#[test]
fn random_exprs() {
    let mut rng = ChaCha8Rng::seed_from_u64(1);
    let expr = random_expr(100, &mut rng);
    println!("{}", expr.len());
    println!("{}", expr.pretty(100));
}

#[test]
fn parallel_bench() {
    let rules_seq = [
        lem_imply(),
        def_imply(),
        def_imply_flip(),
        double_neg(),
        // double_neg_flip(),
        //assoc_or(),
        //dist_and_or(),
        //dist_or_and(),
        //comm_or(),
        //comm_and(),
        lem(),
        or_true(),
        and_true(),
        contrapositive(),
    ];

    let rules = [
        lem_imply_par(),
        def_imply_par(),
        def_imply_flip_par(),
        double_neg_par(),
        // double_neg_flip_par(),
        // assoc_or_par(),
        // dist_and_or_par(),
        // dist_or_and_par(),
        //comm_or_par(),
        //comm_and_par(),
        lem_par(),
        or_true_par(),
        and_true_par(),
        contrapositive_par(),
    ];

    let mut exprs = Vec::new();
    for length in [/*5, 10, 25, 50, 100, 250, 500*/1000, 2500, 5000, 10_000] {
        for seed in 0..10 {
            let mut rng = ChaCha8Rng::seed_from_u64(seed);
            let expr = random_expr(length, &mut rng);
            exprs.push(expr);
        }
    }

    let mut log = String::from(test::csv_header());

    log += &crate::test::parallel_bench(
        &rules,
        &rules_seq,
        &exprs,
        &[
            1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28, 32,
        ],
        "prop-simp-big.csv"
    );

    // std::fs::write("prop-big.csv", log).unwrap();
}
