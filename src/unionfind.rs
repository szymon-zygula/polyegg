use crate::{AtomicId, Id};

use std::fmt::Debug;
use std::sync::atomic::Ordering;

#[derive(Debug, Default, Clone)]
#[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct UnionFind {
    // Because the correctness of the structure does not depend on exact shape of the tree but only
    // on the fact whether the root is correct, relaxed atomic operations can be used.
    // They may race not produce the same structure as a sequential algorithm, but the structure
    // is going to be correct nonetheless, at minimal synchronization cost.
    parents: Vec<AtomicId>,
    next_set: AtomicId,
}

impl UnionFind {
    pub fn make_set(&mut self) -> Id {
        let id = *self.next_set.0.get_mut();
        *self.next_set.0.get_mut() += 1;
        self.parents.push(AtomicId::from(id));
        Id(id)
    }

    /// Returns `Id` of a new set without actually creating this set. The id, however, is correct
    /// and can be created in parallel without any allocations or other modifications of `UnionFind`
    /// and actualized with `create_promised_sets`.
    pub fn promise_set(&self) -> Id {
        Id(self.next_set.0.fetch_add(1, Ordering::Relaxed))
    }

    /// Creates all sets promised by `promise_set`
    pub fn create_promised_sets(&mut self) {
        let mut current_id = self.parents.len();
        self.parents
            .resize_with(*self.next_set.0.get_mut() as usize, || {
                current_id += 1;
                AtomicId::from(current_id - 1)
            });
    }

    pub fn size(&self) -> usize {
        self.parents.len()
    }

    fn parent(&self, query: Id) -> &AtomicId {
        &self.parents[usize::from(query)]
    }

    fn set_parent(&self, query: Id, new_parent: Id) {
        self.parents[usize::from(query)].store_relaxed(new_parent);
    }

    pub fn find(&self, mut current: Id) -> Id {
        // Because another thread might be running the same function, `parent` and `grandparent`
        // might not refer to actual parent and grandparent.
        // However, they are guaranteed to point to some ancestor, which is enough for this
        // function to keep the invariants of the datastructure.
        let mut parent = self.parent(current).load_relaxed();
        while current != parent {
            let grandparent = self.parent(parent).load_relaxed();
            self.set_parent(current, grandparent);
            current = grandparent;
            parent = self.parent(current).load_relaxed();
        }
        current
    }

    /// Checks if `current` is in the union-find structure. If not, returns `None`. If it is, calls
    /// [`Self::find`].
    pub fn try_find(&self, current: Id) -> Option<Id> {
        (self.parents.len() > current.0 as usize).then(|| self.find(current))
    }

    /// Given two leader ids, unions the two eclasses making root1 the leader.
    /// TODO: This function will not work in a multithreaded environment, as we don't know if `root1` and
    /// `root2` are still leaders when calling `self.set_parent`!
    pub fn union(&mut self, root1: Id, root2: Id) -> Id {
        self.set_parent(root2, root1);
        root1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(us: impl IntoIterator<Item = usize>) -> Vec<AtomicId> {
        us.into_iter().map(|u| u.into()).collect()
    }

    #[test]
    fn union_find() {
        let n = 10;
        let id = Id::from;

        let mut uf = UnionFind::default();
        for _ in 0..n {
            uf.make_set();
        }

        // test the initial condition of everyone in their own set
        assert!(ids(0..n)
            .into_iter()
            .zip(uf.parents.iter())
            .all(|(a, b)| a.load_relaxed() == b.load_relaxed()));

        // build up one set
        uf.union(id(0), id(1));
        uf.union(id(0), id(2));
        uf.union(id(0), id(3));

        // build up another set
        uf.union(id(6), id(7));
        uf.union(id(6), id(8));
        uf.union(id(6), id(9));

        // this should compress all paths
        for i in 0..n {
            uf.find(id(i));
        }

        // indexes:         0, 1, 2, 3, 4, 5, 6, 7, 8, 9
        let expected = vec![0, 0, 0, 0, 4, 5, 6, 6, 6, 6];
        assert!(ids(expected)
            .into_iter()
            .zip(uf.parents.iter())
            .all(|(a, b)| a.load_relaxed() == b.load_relaxed()));
    }
}
