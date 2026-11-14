//! Learned clauses -- disjunctions of in/out literals that every extension
//! sought satisfies -- and their propagation by two watched literals.

use crate::algorithms::closure::{assign_literal, Conflict};
use crate::algorithms::lit::{Lit, Reason};
use crate::algorithms::node::Node;

/// The clauses learned so far, each watching two of its literals
#[derive(Debug, Clone)]
pub struct ClauseDb {
    // The clauses: disjunctions of In/Out literals. The first two literals
    // of each are watched: as long as neither is false, the clause cannot be
    // unit or falsified, so it need not be looked at.
    clauses: Vec<Vec<Lit>>,
    // For each argument, the clauses watching a literal that its becoming
    // in, respectively out, makes false -- i.e. watching Out(a) and In(a)
    watch_on_in: Vec<Vec<usize>>,
    watch_on_out: Vec<Vec<usize>>,
}

impl ClauseDb {
    /// An empty database for a framework of `argument_count` arguments
    pub fn new(argument_count: usize) -> ClauseDb {
        ClauseDb {
            clauses: Vec::new(),
            watch_on_in: vec![Vec::new(); argument_count],
            watch_on_out: vec![Vec::new(); argument_count],
        }
    }

    /// Store a learned clause, watching its first two literals, and return
    /// its index. A clause of fewer than two literals gets no watches: it is
    /// either empty, or a unit the caller asserts at level 0 for good.
    // Not called outside tests until the search learns
    #[allow(dead_code)]
    pub fn add_clause(&mut self, literals: Vec<Lit>) -> usize {
        let idx = self.clauses.len();
        if literals.len() >= 2 {
            self.watch(literals[0], idx);
            self.watch(literals[1], idx);
        }
        self.clauses.push(literals);
        idx
    }

    /// Have clause `idx` watch `lit`: it will be looked at when `lit`
    /// becomes false
    pub fn watch(&mut self, lit: Lit, idx: usize) {
        match lit {
            Lit::In(a) => self.watch_on_out[a].push(idx),
            Lit::Out(a) => self.watch_on_in[a].push(idx),
            Lit::Def(_) => unreachable!("clauses have no Def literals"),
        }
    }

    /// Whether any clause is to be looked at now that `assigned` holds
    pub fn has_watches(&self, assigned: Lit) -> bool {
        match assigned {
            Lit::In(a) => !self.watch_on_in[a].is_empty(),
            Lit::Out(a) => !self.watch_on_out[a].is_empty(),
            Lit::Def(_) => false,
        }
    }

    /// Take the list of clauses to look at now that `assigned` holds,
    /// leaving it empty; `put_watches` returns it
    pub fn take_watches(&mut self, assigned: Lit) -> Vec<usize> {
        match assigned {
            Lit::In(a) => std::mem::take(&mut self.watch_on_in[a]),
            Lit::Out(a) => std::mem::take(&mut self.watch_on_out[a]),
            Lit::Def(_) => Vec::new(),
        }
    }

    /// Return a watch list taken with `take_watches`, keeping any watches
    /// added to it in the meantime
    pub fn put_watches(&mut self, assigned: Lit, mut list: Vec<usize>) {
        let slot = match assigned {
            Lit::In(a) => &mut self.watch_on_in[a],
            Lit::Out(a) => &mut self.watch_on_out[a],
            Lit::Def(_) => return,
        };
        list.append(slot);
        *slot = list;
    }

    /// Get the literals of clause `idx`
    pub fn clause(&self, idx: usize) -> &[Lit] {
        &self.clauses[idx]
    }

    /// Get the literals of clause `idx`, to reorder its watches
    pub fn clause_mut(&mut self, idx: usize) -> &mut Vec<Lit> {
        &mut self.clauses[idx]
    }

    /// Get the number of learned clauses stored
    // Not called outside tests until the search learns
    #[allow(dead_code)]
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }
}

/// Look at every learned clause watching a literal that `assigned` has just
/// made false. A clause whose other watched literal is true is left alone;
/// one with another literal that is not false moves its watch there; one
/// with neither is unit, and forces its remaining literal, or falsified.
///
/// Watches need no undoing on backtrack: a clause's two watched literals
/// are only ever both false at a conflict, which backtracking undoes, so
/// after any backtrack neither watched literal is false unless the other
/// is true and was assigned no later -- which is exactly what lets the
/// clause be ignored until a watched literal becomes false again.
pub fn propagate_clauses(assigned: Lit, node: &mut Node) -> Result<(), Conflict> {
    if !node.clauses().has_watches(assigned) {
        // The common case while few clauses are learned, and on the path
        // every assignment takes.
        return Ok(());
    }
    let falsified = assigned.negated();
    let mut list = node.clauses_mut().take_watches(assigned);
    let mut result = Ok(());
    let mut i = 0;
    while i < list.len() {
        let idx = list[i];
        // Keep the literal just falsified second, so the first is the one
        // that may still save the clause.
        let first = {
            let clause = node.clauses_mut().clause_mut(idx);
            if clause[0] == falsified {
                clause.swap(0, 1);
            }
            clause[0]
        };
        if node.lit_value(first) == Some(true) {
            i += 1;
            continue;
        }
        let replacement = node.clauses().clause(idx)[2..]
            .iter()
            .position(|&lit| node.lit_value(lit) != Some(false));
        if let Some(k) = replacement {
            let clause = node.clauses_mut().clause_mut(idx);
            clause.swap(1, k + 2);
            let new_watch = clause[1];
            node.clauses_mut().watch(new_watch, idx);
            list.swap_remove(i);
            continue;
        }
        if node.lit_value(first) == Some(false) {
            result = Err(Conflict::Clause(idx));
            break;
        }
        // Unit: `first` is undecided and every other literal is false.
        assign_literal(first, Reason::Clause(idx), node)
            .expect("an undecided literal cannot clash");
        i += 1;
    }
    node.clauses_mut().put_watches(assigned, list);
    result
}
