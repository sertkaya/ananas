//! Learned clauses -- disjunctions of in/out literals that every extension
//! sought satisfies -- and their propagation by two watched literals.

use crate::algorithms::closure::{assign_literal, Conflict};
use crate::algorithms::lit::{Lit, Reason};
use crate::algorithms::node::Node;

/// How much work propagating the learned clauses did
#[derive(Debug, Default, Clone, Copy)]
pub struct ClauseWork {
    /// Clauses looked at because a watched literal became false
    pub visits: usize,
    /// Literals scanned while looking for a replacement watch
    pub literals_scanned: usize,
    /// Attacks walked: for each propagated literal, its argument's
    /// attackers and victims
    pub attacks_walked: usize,
}

/// A learned clause: a disjunction of In/Out literals, and its literal
/// block distance when it was learned
#[derive(Debug, Clone)]
pub struct Clause {
    // The first two literals are watched: as long as neither is false, the
    // clause cannot be unit or falsified, so it need not be looked at.
    // Empty once the clause has been deleted -- it keeps its index, which
    // reasons on the trail may still name.
    literals: Vec<Lit>,
    lbd: usize,
}

/// The clauses learned so far, each watching two of its literals
#[derive(Debug, Clone)]
pub struct ClauseDb {
    clauses: Vec<Clause>,
    // How many of them have not been deleted
    live: usize,
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
            live: 0,
            watch_on_in: vec![Vec::new(); argument_count],
            watch_on_out: vec![Vec::new(); argument_count],
        }
    }

    /// Delete every clause `doomed` says to, and rebuild the watch lists
    /// from the survivors. Their currently watched literals stay watched:
    /// whatever held for them before holds after. Returns how many were
    /// deleted. The caller must not doom a clause that is the reason for an
    /// assignment still on the trail, nor an empty or unit one.
    pub fn reduce(&mut self, doomed: impl Fn(usize, &[Lit], usize) -> bool) -> usize {
        let mut deleted = 0;
        for idx in 0..self.clauses.len() {
            let clause = &self.clauses[idx];
            if !clause.literals.is_empty() && doomed(idx, &clause.literals, clause.lbd) {
                self.clauses[idx].literals = Vec::new();
                deleted += 1;
            }
        }
        self.live -= deleted;
        for list in self.watch_on_in.iter_mut().chain(self.watch_on_out.iter_mut()) {
            list.clear();
        }
        for idx in 0..self.clauses.len() {
            if self.clauses[idx].literals.len() >= 2 {
                let (first, second) = (self.clauses[idx].literals[0], self.clauses[idx].literals[1]);
                self.watch(first, idx);
                self.watch(second, idx);
            }
        }
        deleted
    }

    /// Whether clause `idx` is still there
    pub fn is_live(&self, idx: usize) -> bool {
        !self.clauses[idx].literals.is_empty()
    }

    /// The literal block distance of clause `idx` when it was learned
    pub fn lbd(&self, idx: usize) -> usize {
        self.clauses[idx].lbd
    }

    /// Store a learned clause with its literal block distance, watching its
    /// first two literals, and return its index. A clause of fewer than two
    /// literals gets no watches: it is either empty, or a unit the caller
    /// asserts at level 0 for good.
    pub fn add_clause(&mut self, literals: Vec<Lit>, lbd: usize) -> usize {
        let idx = self.clauses.len();
        if literals.len() >= 2 {
            self.watch(literals[0], idx);
            self.watch(literals[1], idx);
        }
        self.clauses.push(Clause { literals, lbd });
        self.live += 1;
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

    /// Get the literals of clause `idx`; none if it has been deleted
    pub fn clause(&self, idx: usize) -> &[Lit] {
        &self.clauses[idx].literals
    }

    /// Get the literals of clause `idx`, to reorder its watches
    pub fn clause_mut(&mut self, idx: usize) -> &mut Vec<Lit> {
        &mut self.clauses[idx].literals
    }

    /// Get the number of clause indices handed out, deleted ones included
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    /// Get the number of learned clauses not deleted
    pub fn live_count(&self) -> usize {
        self.live
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
///
/// `work` is told how many clauses were looked at and how many literals
/// scanned for a replacement watch, for the diagnostics.
pub fn propagate_clauses(assigned: Lit, node: &mut Node, work: &mut ClauseWork) -> Result<(), Conflict> {
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
        work.visits += 1;
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
        work.literals_scanned += replacement.map_or(node.clauses().clause(idx).len() - 2, |k| k + 1);
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

#[cfg(test)]
impl Node {
    /// Check the learned clauses against the assignment: none is falsified,
    /// none is unit without having been propagated, and every assignment a
    /// clause forced is the clause's only literal that is not false
    pub fn check_clauses(&self) {
        use crate::algorithms::lit::Value;
        for idx in 0..self.clauses().clause_count() {
            if !self.clauses().is_live(idx) {
                continue;
            }
            let clause = self.clauses().clause(idx);
            let trues = clause.iter().filter(|&&l| self.lit_value(l) == Some(true)).count();
            let undecideds = clause.iter().filter(|&&l| self.lit_value(l).is_none()).count();
            assert!(trues + undecideds > 0, "clause {idx} {clause:?} is falsified");
            assert!(trues > 0 || undecideds > 1, "clause {idx} {clause:?} is unit but not propagated");
        }
        for a in 0..self.value_count() {
            if let (true, Reason::Clause(idx)) = (self.value(a) != Value::Undecided, self.reason(a)) {
                assert!(self.clauses().is_live(idx), "{a}'s reason, clause {idx}, was deleted");
                let clause = self.clauses().clause(idx);
                let others_false = clause.iter()
                    .filter(|&&l| l.arg() != a)
                    .all(|&l| self.lit_value(l) == Some(false));
                let own_true = clause.iter().any(|&l| l.arg() == a && self.lit_value(l) == Some(true));
                assert!(others_false && own_true, "{a} is forced by clause {idx} wrongly");
            }
        }
    }
}
