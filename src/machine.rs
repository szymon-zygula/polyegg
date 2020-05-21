use std::fmt;

use crate::{Analysis, EGraph, ENodeOrVar, Id, Language, PatternAst, Subst, Var};

struct Machine<'a, L> {
    pc: usize,
    reg: Vec<Id>,
    stack: Vec<Binder<'a, L>>,
}

impl<'a, L> Default for Machine<'a, L> {
    fn default() -> Self {
        Self {
            pc: 0,
            reg: vec![],
            stack: vec![],
        }
    }
}

type Addr = usize;
type Reg = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction<L> {
    Bind(Reg, L, Reg),
    Check(Reg, L),
    Compare(Reg, Reg),
    Yield(Vec<Reg>),
}

struct Binder<'a, L> {
    out: Reg,
    next: Addr,
    nodes: std::slice::Iter<'a, L>,
    // in debug mode, we keep the node around to make sure that it matches
    #[cfg(debug_assertions)]
    node: L,
}

impl<'a, L: Language> Binder<'a, L> {
    #[inline(never)]
    fn new(out: Reg, next: Addr, node: &'a L, nodes: &'a [L]) -> Self {
        let slice_iter = if nodes.len() < 100 {
            let mut iter = nodes.iter();
            match iter.position(|n| node.matches(n)) {
                None => [].iter(),
                Some(start) => match iter.position(|n| !node.matches(n)) {
                    None => nodes[start..].iter(),
                    Some(offset) => nodes[start..start + offset + 1].iter(),
                },
            }
        } else {
            let zero = node.clone().map_children(|_| 0);
            let start = nodes.binary_search(&zero).unwrap_or_else(|i| i);
            let big = zero.map_children(|_| Id::MAX);
            let offset = nodes[start..]
                .binary_search(&big)
                .expect_err("Shouldn't be a matching enode");
            nodes[start..start + offset].iter()
        };
        Self {
            out,
            next,
            nodes: slice_iter,
            #[cfg(debug_assertions)]
            node: node.clone(),
        }
    }

    #[inline]
    fn next(&mut self) -> Option<&'a L> {
        let n = self.nodes.next()?;
        #[cfg(debug_assertions)]
        assert!(self.node.matches(n));
        Some(n)
    }
}

use Instruction::*;

impl<'a, L: Language> Machine<'a, L> {
    #[must_use]
    fn backtrack(&mut self) -> Option<()> {
        log::trace!("Backtracking, stack size: {}", self.stack.len());
        loop {
            let binder = self.stack.last_mut()?;
            let next = binder.next;

            if let Some(matched) = binder.next() {
                log::trace!("Binding: {:?}", matched);
                let new_len = binder.out + matched.len();
                self.reg.resize(new_len, 0);
                let mut i = binder.out;
                matched.for_each(|id| {
                    self.reg[i] = id;
                    i += 1;
                });
                debug_assert_eq!(i, new_len);
                self.pc = next;
                return Some(());
            } else {
                self.stack.pop().expect("we know the stack isn't empty");
            }
        }
    }

    fn run<N>(
        &mut self,
        egraph: &'a EGraph<L, N>,
        program: &'a [Instruction<L>],
        mut yield_fn: impl FnMut(&Self, &[Reg]),
    ) where
        N: Analysis<L>,
    {
        macro_rules! backtrack {
            () => {
                if self.backtrack().is_none() {
                    return;
                }
            };
        }

        loop {
            let instr = &program[self.pc];
            self.pc += 1;

            log::trace!("Executing {:?}", instr);

            match instr {
                Bind(i, node, out) => {
                    let eclass = &egraph[self.reg[*i]];
                    self.stack
                        .push(Binder::new(*out, self.pc, node, &eclass.nodes));
                    backtrack!();
                }
                Check(i, t) => {
                    debug_assert!(t.is_leaf());
                    let id = self.reg[*i];
                    let eclass = &egraph[id];
                    if !eclass.nodes.contains(t) {
                        backtrack!()
                    }
                    // TODO the below is more efficient, but is broken
                    // because we don't support look up of ground
                    // terms, because people can just push into eclasses
                    //
                    // let id1 = self.find_reg(*i);
                    // let id2 = self.egraph.get_leaf(t.clone());

                    // if Some(id1) == id2 {
                    //     trace!("Check(r{} = e{}, {:?}) passed", i, id1, t);
                    // } else {
                    //     trace!("Check(r{} = e{}, {:?}) failed", i, id1, t);
                    //     // self.backtrack()?;
                    // }
                }
                Compare(i, j) => {
                    if egraph.find(self.reg[*i]) != egraph.find(self.reg[*j]) {
                        backtrack!()
                    }
                }
                Yield(regs) => {
                    // let ids = regs.iter().map(|r| self.reg[*r]).collect();
                    // backtrack, but don't fail so we can yield
                    yield_fn(self, regs);
                    backtrack!()
                    // return Some(ids);
                }
            }
        }
    }
}

type RegToPat<N> = indexmap::IndexMap<Reg, ENodeOrVar<N>>;
type VarToReg = indexmap::IndexMap<Var, Reg>;

// fn size<N: ENode>(p: &[ENodeOrVar<N>], root: u32) -> usize {
//     match &p[root as usize] {
//         ENodeOrVar::ENode(e) => 1 + e.children().iter().map(|i| size(p, *i)).sum::<usize>(),
//         ENodeOrVar::Var(_) => 1,
//     }
// }

// fn n_free<N: ENode>(v2r: &VarToReg, p: &[ENodeOrVar<N>], root: u32) -> usize {
//     match &p[root as usize] {
//         ENodeOrVar::ENode(e) => e.children().iter().map(|i| n_free(v2r, p, *i)).sum::<usize>(),
//         ENodeOrVar::Var(v) => !v2r.contains_key(v) as usize,
//     }
// }

// fn rank<N: ENode>(v2r: &VarToReg, p1: &[ENodeOrVar<N>], p2: &[ENodeOrVar<N>], root1: u32, root2: u32) -> Ordering {
//     let cost1 = (n_free(v2r, p1, 0), size(p1, 0));
//     let cost2 = (n_free(v2r, p2, 0), size(p2, 0));
//     cost1.cmp(&cost2)
// }

fn compile<L: Language>(
    pattern: &[ENodeOrVar<L>],
    r2p: &mut RegToPat<L>,
    v2r: &mut VarToReg,
    mut next_reg: Reg,
    buf: &mut Vec<Instruction<L>>,
) {
    while let Some((reg, pat)) = r2p.pop() {
        match pat {
            ENodeOrVar::ENode(e) if e.is_leaf() => {
                // e is a ground term, it has no children
                buf.push(Check(reg, e))
            }
            ENodeOrVar::Var(v) => {
                if let Some(&r) = v2r.get(&v) {
                    buf.push(Compare(r, reg))
                } else {
                    v2r.insert(v, reg);
                }
            }
            ENodeOrVar::ENode(e) => {
                assert!(!e.is_leaf());
                buf.push(Bind(reg, e.clone(), next_reg));

                e.for_each_i(|i, child| {
                    r2p.insert(next_reg + i, pattern[child as usize].clone());
                });

                // sort in reverse order so we pop the cheapest
                // NOTE, this doesn't seem to have a very large effect right now
                // TODO restore sorting
                // r2p.sort_by(|_, p1, _, p2| rank(v2r, p1, p2).reverse());
                // r2p.sort_keys();
                // r2p.sort_by(|_, p1, _, p2| p1.cmp(p2).reverse());
                next_reg += e.len();
            }
        }
    }

    assert!(r2p.is_empty());
    let registers = v2r.values().copied().collect();
    buf.push(Yield(registers));
}

#[derive(PartialEq, Clone)]
pub struct Program<L> {
    v2r: VarToReg,
    instrs: Vec<Instruction<L>>,
}

impl<L: fmt::Debug> fmt::Debug for Program<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Program")?;
        for (i, instr) in self.instrs.iter().enumerate() {
            writeln!(f, "{}: {:?}", i, instr)?;
        }
        Ok(())
    }
}

impl<L: Language> Program<L> {
    pub(crate) fn compile_from_pat(pattern: &PatternAst<L>) -> Program<L> {
        let mut instrs = Vec::new();
        let mut r2p = RegToPat::new();
        let mut v2r = VarToReg::new();

        r2p.insert(0, pattern.as_ref().last().unwrap().clone());
        compile(pattern.as_ref(), &mut r2p, &mut v2r, 1, &mut instrs);

        let program = Program { instrs, v2r };
        log::debug!("Compiled {:?} to {:?}", pattern.as_ref(), program);
        program
    }

    pub fn run<A>(&self, egraph: &EGraph<L, A>, eclass: Id) -> Vec<Subst>
    where
        A: Analysis<L>,
    {
        let mut machine = Machine::default();

        assert_eq!(machine.reg.len(), 0);
        machine.reg.push(eclass);

        let mut substs = Vec::new();
        machine.run(egraph, &self.instrs, |machine, regs| {
            let mut s = Subst::default();
            let ids = regs.iter().map(|r| machine.reg[*r]);
            for (i, id) in ids.enumerate() {
                let var = self.v2r.get_index(i).unwrap().0;
                s.insert(var.clone(), id);
            }
            substs.push(s)
        });

        log::trace!("Ran program, found {:?}", substs);
        substs
    }
}
