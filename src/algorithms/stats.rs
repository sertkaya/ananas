//! Diagnostics about a search, printed in verbose mode.

use std::fmt::{Display, Formatter};
use crate::algorithms::learning::Learned;

/// Search diagnostics gathered by a solver for a `verbose` print
#[derive(Default)]
pub struct Stats {
    pub decisions: usize,
    // Calls of the closure: one per decision, per learned clause asserted,
    // and per set of assumptions
    pub propagations: usize,
    pub conflicts: usize,
    // How many learned clauses are stored
    pub clauses: usize,
    // The learned clauses: how long they are, how many literals
    // minimization took off them, and how many decision levels each jumped
    // back over -- chronological backtracking would always be exactly one
    learned_literals_sum: usize,
    learned_literals_max: usize,
    minimized_away_sum: usize,
    backjump_sum: usize,
    backjump_max: usize,
    nonchronological_backjumps: usize,
}

impl Stats {
    /// Record a clause learned from a conflict at decision level `level`
    pub fn record_learned(&mut self, learned: &Learned, level: usize) {
        let jump = level - learned.assertion_level;
        self.conflicts += 1;
        self.learned_literals_sum += learned.literals.len();
        self.learned_literals_max = self.learned_literals_max.max(learned.literals.len());
        self.minimized_away_sum += learned.unminimized_len - learned.literals.len();
        self.backjump_sum += jump;
        self.backjump_max = self.backjump_max.max(jump);
        if jump > 1 {
            self.nonchronological_backjumps += 1;
        }
    }
}

impl Display for Stats {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let average = |sum: usize, count: usize| {
            if count > 0 { sum as f64 / count as f64 } else { 0.0 }
        };
        write!(
            f,
            "decisions={} propagations={} conflicts={} clauses={} learned_len_avg={:.1} learned_len_max={} \
             minimized_away_avg={:.1} backjump_avg={:.2} backjump_max={} nonchronological_backjumps={}",
            self.decisions,
            self.propagations,
            self.conflicts,
            self.clauses,
            average(self.learned_literals_sum, self.conflicts),
            self.learned_literals_max,
            average(self.minimized_away_sum, self.conflicts),
            average(self.backjump_sum, self.conflicts),
            self.backjump_max,
            self.nonchronological_backjumps,
        )
    }
}
