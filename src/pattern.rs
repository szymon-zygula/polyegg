use fmt::Formatter;
use log::*;
use std::borrow::Cow;
use std::fmt::{self, Display};
use std::{convert::TryFrom, str::FromStr};

use thiserror::Error;

use rayon::prelude::*;

use crate::*;

use self::egraph::EGraphChannel;
use self::rewrite::ParallelApplier;

/// A pattern that can function as either a [`Searcher`] or [`Applier`].
///
/// A [`Pattern`] is essentially a for-all quantified expression with
/// [`Var`]s as the variables (in the logical sense).
///
/// When creating a [`Rewrite`], the most common thing to use as either
/// the left hand side (the [`Searcher`]) or the right hand side
/// (the [`Applier`]) is a [`Pattern`].
///
/// As a [`Searcher`], a [`Pattern`] does the intuitive
/// thing.
/// Here is a somewhat verbose formal-ish statement:
/// Searching for a pattern in an egraph yields substitutions
/// ([`Subst`]s) _s_ such that, for any _s'_—where instead of
/// mapping a variables to an eclass as _s_ does, _s'_ maps
/// a variable to an arbitrary expression represented by that
/// eclass—_p[s']_ (the pattern under substitution _s'_) is also
/// represented by the egraph.
///
/// As an [`Applier`], a [`Pattern`] performs the given substitution
/// and adds the result to the [`EGraph`].
///
/// Importantly, [`Pattern`] implements [`FromStr`] if the
/// [`Language`] does.
/// This is probably how you'll create most [`Pattern`]s.
///
/// ```
/// use egg::*;
/// define_language! {
///     enum Math {
///         Num(i32),
///         "+" = Add([Id; 2]),
///     }
/// }
///
/// let mut egraph = EGraph::<Math, ()>::default();
/// let a11 = egraph.add_expr(&"(+ 1 1)".parse().unwrap());
/// let a22 = egraph.add_expr(&"(+ 2 2)".parse().unwrap());
///
/// // use Var syntax (leading question mark) to get a
/// // variable in the Pattern
/// let same_add: Pattern<Math> = "(+ ?a ?a)".parse().unwrap();
///
/// // Rebuild before searching
/// egraph.rebuild();
///
/// // This is the search method from the Searcher trait
/// let matches = same_add.search(&egraph);
/// let matched_eclasses: Vec<Id> = matches.iter().map(|m| m.eclass).collect();
/// assert_eq!(matched_eclasses, vec![a11, a22]);
/// ```
///
/// [`FromStr`]: std::str::FromStr
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Pattern<L> {
    /// The actual pattern as a [`RecExpr`]
    pub ast: PatternAst<L>,
    program: machine::Program<L>,
}

/// A [`RecExpr`] that represents a
/// [`Pattern`].
pub type PatternAst<L> = RecExpr<ENodeOrVar<L>>;

impl<L: Language> PatternAst<L> {
    /// Returns a new `PatternAst` with the variables renames canonically
    pub fn alpha_rename(&self) -> Self {
        let mut vars = HashMap::<Var, Var>::default();
        let mut new = PatternAst::default();

        fn mkvar(i: usize) -> Var {
            let vs = &["?x", "?y", "?z", "?w"];
            match vs.get(i) {
                Some(v) => v.parse().unwrap(),
                None => format!("?v{}", i - vs.len()).parse().unwrap(),
            }
        }

        for n in self.as_ref() {
            new.add(match n {
                ENodeOrVar::ENode(_) => n.clone(),
                ENodeOrVar::Var(v) => {
                    let i = vars.len();
                    ENodeOrVar::Var(*vars.entry(*v).or_insert_with(|| mkvar(i)))
                }
            });
        }

        new
    }
}

impl<L: Language> Pattern<L> {
    /// Creates a new pattern from the given pattern ast.
    pub fn new(ast: PatternAst<L>) -> Self {
        let ast = ast.compact();
        let program = machine::Program::compile_from_pat(&ast);
        Pattern { ast, program }
    }

    /// Returns a list of the [`Var`]s in this pattern.
    pub fn vars(&self) -> Vec<Var> {
        let mut vars = vec![];
        for n in self.ast.as_ref() {
            if let ENodeOrVar::Var(v) = n {
                if !vars.contains(v) {
                    vars.push(*v)
                }
            }
        }
        vars
    }
}

impl<L: Language + Display> Pattern<L> {
    /// Pretty print this pattern as a sexp with the given width
    pub fn pretty(&self, width: usize) -> String {
        self.ast.pretty(width)
    }
}

/// The language of [`Pattern`]s.
///
#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum ENodeOrVar<L> {
    /// An enode from the underlying [`Language`]
    ENode(L),
    /// A pattern variable
    Var(Var),
}

impl<L: Language> Language for ENodeOrVar<L> {
    fn matches(&self, _other: &Self) -> bool {
        panic!("Should never call this")
    }

    fn children(&self) -> &[Id] {
        match self {
            ENodeOrVar::ENode(n) => n.children(),
            ENodeOrVar::Var(_) => &[],
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            ENodeOrVar::ENode(n) => n.children_mut(),
            ENodeOrVar::Var(_) => &mut [],
        }
    }
}

impl<L: Language + Display> Display for ENodeOrVar<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ENode(node) => Display::fmt(node, f),
            Self::Var(var) => Display::fmt(var, f),
        }
    }
}

#[derive(Debug, Error)]
pub enum ENodeOrVarParseError<E> {
    #[error(transparent)]
    BadVar(<Var as FromStr>::Err),

    #[error("tried to parse pattern variable {0:?} as an operator")]
    UnexpectedVar(String),

    #[error(transparent)]
    BadOp(E),
}

impl<L: FromOp> FromOp for ENodeOrVar<L> {
    type Error = ENodeOrVarParseError<L::Error>;

    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        use ENodeOrVarParseError::*;

        if op.starts_with('?') && op.len() > 1 {
            if children.is_empty() {
                op.parse().map(Self::Var).map_err(BadVar)
            } else {
                Err(UnexpectedVar(op.to_owned()))
            }
        } else {
            L::from_op(op, children).map(Self::ENode).map_err(BadOp)
        }
    }
}

impl<L: FromOp> std::str::FromStr for Pattern<L> {
    type Err = RecExprParseError<ENodeOrVarParseError<L::Error>>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        PatternAst::from_str(s).map(Self::from)
    }
}

impl<'a, L: Language> From<&'a [L]> for Pattern<L> {
    fn from(expr: &'a [L]) -> Self {
        let nodes: Vec<_> = expr.iter().cloned().map(ENodeOrVar::ENode).collect();
        let ast = RecExpr::from(nodes);
        Self::new(ast)
    }
}

impl<L: Language> From<&RecExpr<L>> for Pattern<L> {
    fn from(expr: &RecExpr<L>) -> Self {
        Self::from(expr.as_ref())
    }
}

impl<L: Language> From<PatternAst<L>> for Pattern<L> {
    fn from(ast: PatternAst<L>) -> Self {
        Self::new(ast)
    }
}

impl<L: Language> TryFrom<Pattern<L>> for RecExpr<L> {
    type Error = Var;
    fn try_from(pat: Pattern<L>) -> Result<Self, Self::Error> {
        let nodes = pat.ast.as_ref().iter().cloned();
        let ns: Result<Vec<_>, _> = nodes
            .map(|n| match n {
                ENodeOrVar::ENode(n) => Ok(n),
                ENodeOrVar::Var(v) => Err(v),
            })
            .collect();
        ns.map(RecExpr::from)
    }
}

impl<L: Language + Display> Display for Pattern<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.ast, f)
    }
}

/// The result of searching a [`Searcher`] over one eclass.
///
/// Note that one [`SearchMatches`] can contain many found
/// substitutions. So taking the length of a list of [`SearchMatches`]
/// tells you how many eclasses something was matched in, _not_ how
/// many matches were found total.
///
#[derive(Debug)]
pub struct SearchMatches<'a, L: Language> {
    /// The eclass id that these matches were found in.
    pub eclass: Id,
    /// The substitutions for each match.
    pub substs: Vec<Subst>,
    /// Optionally, an ast for the matches used in proof production.
    pub ast: Option<Cow<'a, PatternAst<L>>>,
}

impl<L: Language, A: Analysis<L>> Searcher<L, A> for Pattern<L> {
    fn get_pattern_ast(&self) -> Option<&PatternAst<L>> {
        Some(&self.ast)
    }

    fn search_with_limit(&self, egraph: &EGraph<L, A>, limit: usize) -> Vec<SearchMatches<L>> {
        match self.ast.as_ref().last().unwrap() {
            ENodeOrVar::ENode(e) => {
                #[allow(enum_intrinsics_non_enums)]
                let key = std::mem::discriminant(e);
                match egraph.classes_by_op.get(&key) {
                    None => vec![],
                    Some(ids) => rewrite::search_eclasses_with_limit(
                        self,
                        egraph,
                        ids.par_iter().cloned(),
                        limit,
                    ),
                }
            }
            ENodeOrVar::Var(_) => rewrite::search_eclasses_with_limit(
                self,
                egraph,
                egraph.par_classes().map(|e| e.id),
                limit,
            ),
        }
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<L, A>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<L>> {
        let substs = self.program.run_with_limit(egraph, eclass, limit);
        if substs.is_empty() {
            None
        } else {
            let ast = Some(Cow::Borrowed(&self.ast));
            Some(SearchMatches {
                eclass,
                substs,
                ast,
            })
        }
    }

    fn vars(&self) -> Vec<Var> {
        Pattern::vars(self)
    }
}

impl<L, N> Applier<L, N> for Pattern<L>
where
    L: Language,
    N: Analysis<L>,
{
    fn get_pattern_ast(&self) -> Option<&PatternAst<L>> {
        Some(&self.ast)
    }

    fn apply_matches(
        &self,
        egraph: &mut EGraph<L, N>,
        matches: &[SearchMatches<L>],
        rule_name: Symbol,
    ) -> Vec<Id> {
        let mut added = vec![];
        let ast = self.ast.as_ref();
        let mut id_buf = vec![0.into(); ast.len()];
        for mat in matches {
            let sast = mat.ast.as_ref().map(|cow| cow.as_ref());
            for subst in &mat.substs {
                let did_something;
                let id;
                if egraph.are_explanations_enabled() {
                    let (id_temp, did_something_temp) =
                        egraph.union_instantiations(sast.unwrap(), &self.ast, subst, rule_name);
                    did_something = did_something_temp;
                    id = id_temp;
                } else {
                    id = apply_pat(&mut id_buf, ast, egraph, subst);
                    did_something = egraph.union(id, mat.eclass);
                }

                if did_something {
                    added.push(id)
                }
            }
        }
        added
    }

    fn apply_one(
        &self,
        egraph: &mut EGraph<L, N>,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<L>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let ast = self.ast.as_ref();
        let mut id_buf = vec![0.into(); ast.len()];
        // Id of the class containing the new node
        let id = apply_pat(&mut id_buf, ast, egraph, subst);

        if let Some(ast) = searcher_ast {
            let (from, did_something) =
                egraph.union_instantiations(ast, &self.ast, subst, rule_name);
            if did_something {
                vec![from]
            } else {
                vec![]
            }
        } else if egraph.union(eclass, id) {
            vec![eclass]
        } else {
            vec![]
        }
    }

    fn vars(&self) -> Vec<Var> {
        Pattern::vars(self)
    }
}

pub(crate) fn apply_pat<L: Language, A: Analysis<L>>(
    ids: &mut [Id],
    pat: &[ENodeOrVar<L>],
    egraph: &mut EGraph<L, A>,
    subst: &Subst,
) -> Id {
    debug_assert_eq!(pat.len(), ids.len());
    trace!("apply_rec {:2?} {:?}", pat, subst);

    for (i, pat_node) in pat.iter().enumerate() {
        let id = match pat_node {
            ENodeOrVar::Var(w) => subst[*w],
            ENodeOrVar::ENode(e) => {
                let n = e.clone().map_children(|child| ids[usize::from(child)]);
                trace!("adding: {:?}", n);
                egraph.add(n)
            }
        };
        ids[i] = id;
    }

    *ids.last().unwrap()
}

impl<L, N> ParallelApplier<L, N> for Pattern<L>
where
    L: Language,
    N: Analysis<L>,
{
    fn apply_matches_par(
        &self,
        egraph_channel: &EGraphChannel<L, N>,
        matches: &[SearchMatches<L>],
        _rule_name: Symbol,
    ) {
        let ast = self.ast.as_ref();

        matches.par_iter().for_each(|mat| {
            mat.substs.par_iter().for_each(|subst| {
                let mut egraph_channel = egraph_channel.clone();
                let id = apply_pat_par_safe::<L, N>(ast, &mut egraph_channel, subst);
                egraph_channel.flush_additions();
                egraph_channel.union(id, mat.eclass);
            });
        });
    }

    fn apply_one_par(
        &self,
        egraph_channel: &EGraphChannel<L, N>,
        eclass: Id,
        subst: &Subst,
        _rule_name: Symbol,
    ) {
        // Id of the class containing the new node
        let id = apply_pat_par_safe::<L, N>(&self.ast.as_ref(), &mut egraph_channel.clone(), subst);
        egraph_channel.union(eclass, id);
    }
}

pub(crate) fn apply_pat_par_safe<L, N>(
    pat: &[ENodeOrVar<L>],
    egraph_channel: &mut EGraphChannel<L, N>,
    subst: &Subst,
) -> Id
where
    L: Language,
    N: Analysis<L>,
{
    let mut ids = vec![0.into(); pat.len()];
    trace!("apply_rec {:2?} {:?}", pat, subst);

    egraph_channel.reserve_additions_buffer(pat.len());

    for (i, pat_node) in pat.iter().enumerate() {
        let id = match pat_node {
            ENodeOrVar::Var(w) => subst[*w],
            ENodeOrVar::ENode(e) => {
                let n = e.clone().map_children(|child| ids[usize::from(child)]);
                trace!("adding: {:?}", n);
                egraph_channel.add(n)
            }
        };
        ids[i] = id;
    }

    *ids.last().unwrap()
}

#[cfg(test)]
mod tests {

    use crate::{SymbolLang as S, *};

    type EGraph = crate::EGraph<S, ()>;

    #[test]
    fn simple_match() {
        crate::init_logger();
        let mut egraph = EGraph::default();

        let (plus_id, _) = egraph.union_instantiations(
            &"(+ x y)".parse().unwrap(),
            &"(+ z w)".parse().unwrap(),
            &Default::default(),
            "union_plus".to_string(),
        );
        egraph.rebuild();

        let commute_plus = rewrite!(
            "commute_plus";
            "(+ ?a ?b)" => "(+ ?b ?a)"
        );

        let matches = commute_plus.search(&egraph);
        let n_matches: usize = matches.iter().map(|m| m.substs.len()).sum();
        assert_eq!(n_matches, 2, "matches is wrong: {:#?}", matches);

        let applications = commute_plus.apply(&mut egraph, &matches);
        egraph.rebuild();
        assert_eq!(applications.len(), 2);

        let actual_substs: Vec<Subst> = matches.iter().flat_map(|m| m.substs.clone()).collect();

        println!("Here are the substs!");
        for m in &actual_substs {
            println!("substs: {:?}", m);
        }

        egraph.dot().to_dot("target/simple-match.dot").unwrap();

        use crate::extract::{AstSize, Extractor};

        let ext = Extractor::new(&egraph, AstSize);
        let (_, best) = ext.find_best(plus_id);
        eprintln!("Best: {:#?}", best);
    }

    #[test]
    fn nonlinear_patterns() {
        crate::init_logger();
        let mut egraph = EGraph::default();
        egraph.add_expr(&"(f a a)".parse().unwrap());
        egraph.add_expr(&"(f a (g a))))".parse().unwrap());
        egraph.add_expr(&"(f a (g b))))".parse().unwrap());
        egraph.add_expr(&"(h (foo a b) 0 1)".parse().unwrap());
        egraph.add_expr(&"(h (foo a b) 1 0)".parse().unwrap());
        egraph.add_expr(&"(h (foo a b) 0 0)".parse().unwrap());
        egraph.rebuild();

        let n_matches = |s: &str| s.parse::<Pattern<S>>().unwrap().n_matches(&egraph);

        assert_eq!(n_matches("(f ?x ?y)"), 3);
        assert_eq!(n_matches("(f ?x ?x)"), 1);
        assert_eq!(n_matches("(f ?x (g ?y))))"), 2);
        assert_eq!(n_matches("(f ?x (g ?x))))"), 1);
        assert_eq!(n_matches("(h ?x 0 0)"), 1);
    }

    #[test]
    fn search_with_limit() {
        crate::init_logger();
        let init_expr = &"(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 6)))))".parse().unwrap();
        let rules: Vec<Rewrite<_, ()>> = vec![
            rewrite!("comm"; "(+ ?x ?y)" => "(+ ?y ?x)"),
            rewrite!("assoc"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),
        ];
        let runner = Runner::default().with_expr(init_expr).run(&rules);
        let egraph = &runner.egraph;

        let len = |m: &Vec<SearchMatches<S>>| -> usize { m.iter().map(|m| m.substs.len()).sum() };

        let pat = &"(+ ?x (+ ?y ?z))".parse::<Pattern<S>>().unwrap();
        let m = pat.search(egraph);
        let match_size = 2100;
        assert_eq!(len(&m), match_size);

        for limit in [1, 10, 100, 1000, 10000] {
            let m = pat.search_with_limit(egraph, limit);
            assert_eq!(len(&m), usize::min(limit, match_size));
        }

        let id = egraph.lookup_expr(init_expr).unwrap();
        let m = pat.search_eclass(egraph, id).unwrap();
        let match_size = 540;
        assert_eq!(m.substs.len(), match_size);

        for limit in [1, 10, 100, 1000] {
            let m1 = pat.search_eclass_with_limit(egraph, id, limit).unwrap();
            assert_eq!(m1.substs.len(), usize::min(limit, match_size));
        }
    }

    #[test]
    fn search_with_limit_benchmark() {
        use std::io::Write;
        crate::init_logger();
        let mut init_expr = RecExpr::default();

        let mut last = init_expr.add(SymbolLang::leaf("0"));
        let mut cur;

        print!("Building the tree... ");
        std::io::stdout().flush().unwrap();

        for i in 1..1000000 {
            cur = init_expr.add(SymbolLang::leaf(i.to_string()));
            last = init_expr.add(SymbolLang::new("+", vec![cur, last]));
        }
        println!("Done");

        let rules: Vec<Rewrite<_, ()>> = vec![
            rewrite!("comm"; "(+ ?x ?y)" => "(+ ?y ?x)"),
            rewrite!("assoc"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),
        ];
        print!("Running... ");
        std::io::stdout().flush().unwrap();

        let runner = Runner::default().with_expr(&init_expr).run(&rules);
        let egraph = &runner.egraph;
        println!("Done");

        let pat = &"(+ ?x (+ ?y ?z))".parse::<Pattern<S>>().unwrap();

        for threads in [1, 1, 4, 8, 16] {
            println!("Threads: {}", threads);
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap();

            println!("Installing thread pool...");
            pool.install(|| {
                print!("Starting saturation... ");
                std::io::stdout().flush().unwrap();
                let start = std::time::Instant::now();
                pat.search(egraph);
                let end = std::time::Instant::now();
                println!("Done");
                println!("Whole search time: {}s", (end - start).as_secs_f64());

                for limit in [10, 750, 10000, 100000] {
                    let start = std::time::Instant::now();
                    pat.search_with_limit(egraph, limit);
                    let end = std::time::Instant::now();
                    println!("Parte search time: {}s", (end - start).as_secs_f64());
                }
                println!();
            });
        }
    }

    #[test]
    fn rules_benchmark() {
        use std::io::Write;
        crate::init_logger();
        let mut init_expr = RecExpr::default();

        let mut last = init_expr.add(SymbolLang::leaf("0"));
        let mut cur;

        print!("Building the tree... ");
        std::io::stdout().flush().unwrap();

        for i in 1..100_000 {
            cur = init_expr.add(SymbolLang::leaf((i % 10).to_string()));
            if i % 2 == 0 {
                last = init_expr.add(SymbolLang::new("+", vec![cur, last]));
            } else {
                last = init_expr.add(SymbolLang::new("-", vec![cur, last]));
            }
        }
        println!("Done");

        // let rules_seq: Vec<Rewrite<_, ()>> = vec![
        //     rewrite!("comm"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        //     rewrite!("assoc"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),
        //     rewrite!("ident"; "(+ ?x 0)" => "?x"),
        //     rewrite!("double-neg"; "(- (- ?x))" => "?x"),
        //     rewrite!("unary-plus"; "(+ ?x)" => "?x"),
        //     rewrite!("same-neg"; "(- ?x ?x)" => "0"),
        //     rewrite!("1+1"; "(+ 1 1)" => "2"),
        //     rewrite!("1+2"; "(+ 1 2)" => "3"),
        //     rewrite!("1+3"; "(+ 1 3)" => "4"),
        //     rewrite!("1+4"; "(+ 1 4)" => "5"),
        //     rewrite!("1+5"; "(+ 1 5)" => "6"),
        //     rewrite!("1+6"; "(+ 1 6)" => "7"),
        //     rewrite!("1+7"; "(+ 1 7)" => "8"),
        //     rewrite!("1+8"; "(+ 1 8)" => "9"),
        //     rewrite!("1+9"; "(+ 1 9)" => "10"),
        //     rewrite!("2+1"; "(+ 2 1)" => "3"),
        //     rewrite!("2+2"; "(+ 2 2)" => "4"),
        //     rewrite!("2+3"; "(+ 2 3)" => "5"),
        //     rewrite!("2+4"; "(+ 2 4)" => "6"),
        //     rewrite!("2+5"; "(+ 2 5)" => "7"),
        //     rewrite!("2+6"; "(+ 2 6)" => "8"),
        //     rewrite!("2+7"; "(+ 2 7)" => "9"),
        //     rewrite!("2+8"; "(+ 2 8)" => "10"),
        //     rewrite!("2+9"; "(+ 2 9)" => "11"),
        //     rewrite!("3+1"; "(+ 3 1)" => "4"),
        //     rewrite!("3+2"; "(+ 3 2)" => "5"),
        //     rewrite!("3+3"; "(+ 3 3)" => "6"),
        //     rewrite!("3+4"; "(+ 3 4)" => "7"),
        //     rewrite!("3+5"; "(+ 3 5)" => "8"),
        //     rewrite!("3+6"; "(+ 3 6)" => "9"),
        //     rewrite!("3+7"; "(+ 3 7)" => "10"),
        //     rewrite!("3+8"; "(+ 3 8)" => "11"),
        //     rewrite!("3+9"; "(+ 3 9)" => "12"),
        //     rewrite!("4+1"; "(+ 4 1)" => "5"),
        //     rewrite!("4+2"; "(+ 4 2)" => "6"),
        //     rewrite!("4+3"; "(+ 4 3)" => "7"),
        //     rewrite!("4+4"; "(+ 4 4)" => "8"),
        //     rewrite!("4+5"; "(+ 4 5)" => "9"),
        //     rewrite!("4+6"; "(+ 4 6)" => "10"),
        //     rewrite!("4+7"; "(+ 4 7)" => "11"),
        //     rewrite!("4+8"; "(+ 4 8)" => "12"),
        //     rewrite!("4+9"; "(+ 4 9)" => "13"),
        //     rewrite!("5+1"; "(+ 5 1)" => "6"),
        //     rewrite!("5+2"; "(+ 5 2)" => "7"),
        //     rewrite!("5+3"; "(+ 5 3)" => "8"),
        //     rewrite!("5+4"; "(+ 5 4)" => "9"),
        //     rewrite!("5+5"; "(+ 5 5)" => "10"),
        //     rewrite!("5+6"; "(+ 5 6)" => "11"),
        //     rewrite!("5+7"; "(+ 5 7)" => "12"),
        //     rewrite!("5+8"; "(+ 5 8)" => "13"),
        //     rewrite!("5+9"; "(+ 5 9)" => "14"),
        //     rewrite!("6+1"; "(+ 6 1)" => "7"),
        //     rewrite!("6+2"; "(+ 6 2)" => "8"),
        //     rewrite!("6+3"; "(+ 6 3)" => "9"),
        //     rewrite!("6+4"; "(+ 6 4)" => "10"),
        //     rewrite!("6+5"; "(+ 6 5)" => "11"),
        //     rewrite!("6+6"; "(+ 6 6)" => "12"),
        //     rewrite!("6+7"; "(+ 6 7)" => "13"),
        //     rewrite!("6+8"; "(+ 6 8)" => "14"),
        //     rewrite!("6+9"; "(+ 6 9)" => "15"),
        //     rewrite!("7+1"; "(+ 7 1)" => "8"),
        //     rewrite!("7+2"; "(+ 7 2)" => "9"),
        //     rewrite!("7+3"; "(+ 7 3)" => "10"),
        //     rewrite!("7+4"; "(+ 7 4)" => "11"),
        //     rewrite!("7+5"; "(+ 7 5)" => "12"),
        //     rewrite!("7+6"; "(+ 7 6)" => "13"),
        //     rewrite!("7+7"; "(+ 7 7)" => "14"),
        //     rewrite!("7+8"; "(+ 7 8)" => "15"),
        //     rewrite!("7+9"; "(+ 7 9)" => "16"),
        //     rewrite!("8+1"; "(+ 8 1)" => "9"),
        //     rewrite!("8+2"; "(+ 8 2)" => "10"),
        //     rewrite!("8+3"; "(+ 8 3)" => "11"),
        //     rewrite!("8+4"; "(+ 8 4)" => "12"),
        //     rewrite!("8+5"; "(+ 8 5)" => "13"),
        //     rewrite!("8+6"; "(+ 8 6)" => "14"),
        //     rewrite!("8+7"; "(+ 8 7)" => "15"),
        //     rewrite!("8+8"; "(+ 8 8)" => "16"),
        //     rewrite!("8+9"; "(+ 8 9)" => "17"),
        //     rewrite!("9+1"; "(+ 9 1)" => "10"),
        //     rewrite!("9+2"; "(+ 9 2)" => "11"),
        //     rewrite!("9+3"; "(+ 9 3)" => "12"),
        //     rewrite!("9+4"; "(+ 9 4)" => "13"),
        //     rewrite!("9+5"; "(+ 9 5)" => "14"),
        //     rewrite!("9+6"; "(+ 9 6)" => "15"),
        //     rewrite!("9+7"; "(+ 9 7)" => "16"),
        //     rewrite!("9+8"; "(+ 9 8)" => "17"),
        //     rewrite!("9+9"; "(+ 9 9)" => "18"),
        // ];

        let rules: Vec<ParallelRewrite<_, ()>> = vec![
            rewrite_par!("comm"; "(+ ?x ?y)" => "(+ ?y ?x)"),
            rewrite_par!("assoc"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),
            rewrite_par!("ident"; "(+ ?x 0)" => "?x"),
            rewrite_par!("double-neg"; "(- (- ?x))" => "?x"),
            rewrite_par!("unary-plus"; "(+ ?x)" => "?x"),
            rewrite_par!("same-neg"; "(- ?x ?x)" => "0"),
            rewrite_par!("1+1"; "(+ 1 1)" => "2"),
            rewrite_par!("1+2"; "(+ 1 2)" => "3"),
            rewrite_par!("1+3"; "(+ 1 3)" => "4"),
            rewrite_par!("1+4"; "(+ 1 4)" => "5"),
            rewrite_par!("1+5"; "(+ 1 5)" => "6"),
            rewrite_par!("1+6"; "(+ 1 6)" => "7"),
            rewrite_par!("1+7"; "(+ 1 7)" => "8"),
            rewrite_par!("1+8"; "(+ 1 8)" => "9"),
            rewrite_par!("1+9"; "(+ 1 9)" => "10"),
            rewrite_par!("2+1"; "(+ 2 1)" => "3"),
            rewrite_par!("2+2"; "(+ 2 2)" => "4"),
            rewrite_par!("2+3"; "(+ 2 3)" => "5"),
            rewrite_par!("2+4"; "(+ 2 4)" => "6"),
            rewrite_par!("2+5"; "(+ 2 5)" => "7"),
            rewrite_par!("2+6"; "(+ 2 6)" => "8"),
            rewrite_par!("2+7"; "(+ 2 7)" => "9"),
            rewrite_par!("2+8"; "(+ 2 8)" => "10"),
            rewrite_par!("2+9"; "(+ 2 9)" => "11"),
            rewrite_par!("3+1"; "(+ 3 1)" => "4"),
            rewrite_par!("3+2"; "(+ 3 2)" => "5"),
            rewrite_par!("3+3"; "(+ 3 3)" => "6"),
            rewrite_par!("3+4"; "(+ 3 4)" => "7"),
            rewrite_par!("3+5"; "(+ 3 5)" => "8"),
            rewrite_par!("3+6"; "(+ 3 6)" => "9"),
            rewrite_par!("3+7"; "(+ 3 7)" => "10"),
            rewrite_par!("3+8"; "(+ 3 8)" => "11"),
            rewrite_par!("3+9"; "(+ 3 9)" => "12"),
            rewrite_par!("4+1"; "(+ 4 1)" => "5"),
            rewrite_par!("4+2"; "(+ 4 2)" => "6"),
            rewrite_par!("4+3"; "(+ 4 3)" => "7"),
            rewrite_par!("4+4"; "(+ 4 4)" => "8"),
            rewrite_par!("4+5"; "(+ 4 5)" => "9"),
            rewrite_par!("4+6"; "(+ 4 6)" => "10"),
            rewrite_par!("4+7"; "(+ 4 7)" => "11"),
            rewrite_par!("4+8"; "(+ 4 8)" => "12"),
            rewrite_par!("4+9"; "(+ 4 9)" => "13"),
            rewrite_par!("5+1"; "(+ 5 1)" => "6"),
            rewrite_par!("5+2"; "(+ 5 2)" => "7"),
            rewrite_par!("5+3"; "(+ 5 3)" => "8"),
            rewrite_par!("5+4"; "(+ 5 4)" => "9"),
            rewrite_par!("5+5"; "(+ 5 5)" => "10"),
            rewrite_par!("5+6"; "(+ 5 6)" => "11"),
            rewrite_par!("5+7"; "(+ 5 7)" => "12"),
            rewrite_par!("5+8"; "(+ 5 8)" => "13"),
            rewrite_par!("5+9"; "(+ 5 9)" => "14"),
            rewrite_par!("6+1"; "(+ 6 1)" => "7"),
            rewrite_par!("6+2"; "(+ 6 2)" => "8"),
            rewrite_par!("6+3"; "(+ 6 3)" => "9"),
            rewrite_par!("6+4"; "(+ 6 4)" => "10"),
            rewrite_par!("6+5"; "(+ 6 5)" => "11"),
            rewrite_par!("6+6"; "(+ 6 6)" => "12"),
            rewrite_par!("6+7"; "(+ 6 7)" => "13"),
            rewrite_par!("6+8"; "(+ 6 8)" => "14"),
            rewrite_par!("6+9"; "(+ 6 9)" => "15"),
            rewrite_par!("7+1"; "(+ 7 1)" => "8"),
            rewrite_par!("7+2"; "(+ 7 2)" => "9"),
            rewrite_par!("7+3"; "(+ 7 3)" => "10"),
            rewrite_par!("7+4"; "(+ 7 4)" => "11"),
            rewrite_par!("7+5"; "(+ 7 5)" => "12"),
            rewrite_par!("7+6"; "(+ 7 6)" => "13"),
            rewrite_par!("7+7"; "(+ 7 7)" => "14"),
            rewrite_par!("7+8"; "(+ 7 8)" => "15"),
            rewrite_par!("7+9"; "(+ 7 9)" => "16"),
            rewrite_par!("8+1"; "(+ 8 1)" => "9"),
            rewrite_par!("8+2"; "(+ 8 2)" => "10"),
            rewrite_par!("8+3"; "(+ 8 3)" => "11"),
            rewrite_par!("8+4"; "(+ 8 4)" => "12"),
            rewrite_par!("8+5"; "(+ 8 5)" => "13"),
            rewrite_par!("8+6"; "(+ 8 6)" => "14"),
            rewrite_par!("8+7"; "(+ 8 7)" => "15"),
            rewrite_par!("8+8"; "(+ 8 8)" => "16"),
            rewrite_par!("8+9"; "(+ 8 9)" => "17"),
            rewrite_par!("9+1"; "(+ 9 1)" => "10"),
            rewrite_par!("9+2"; "(+ 9 2)" => "11"),
            rewrite_par!("9+3"; "(+ 9 3)" => "12"),
            rewrite_par!("9+4"; "(+ 9 4)" => "13"),
            rewrite_par!("9+5"; "(+ 9 5)" => "14"),
            rewrite_par!("9+6"; "(+ 9 6)" => "15"),
            rewrite_par!("9+7"; "(+ 9 7)" => "16"),
            rewrite_par!("9+8"; "(+ 9 8)" => "17"),
            rewrite_par!("9+9"; "(+ 9 9)" => "18"),
        ];

        // print!("Running sequential warmup... ");
        // std::io::stdout().flush().unwrap();
        // let runner = Runner::default_par()
        //     .with_node_limit(100_000_000)
        //     .with_time_limit(std::time::Duration::from_secs_f64(60.0))
        //     .with_expr(&init_expr)
        //     .run(&rules_seq);
        // // runner.print_report();
        // println!("Done");
        // print!("Running sequential... ");
        // let runner = Runner::default_par()
        //     .with_node_limit(100_000_000)
        //     .with_time_limit(std::time::Duration::from_secs_f64(150.0))
        //     .with_expr(&init_expr)
        //     .run(&rules_seq);
        // runner.print_report();
        // runner.egraph.dot().to_svg("seq.svg").unwrap();
        // println!("Done");

        crate::test::parallel_bench(rules, &init_expr, &[1, 1, 2]);
    }
}
