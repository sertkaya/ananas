//! Diagnostics about a search, printed in verbose mode.

use std::fmt::{Display, Formatter};
use std::time::Duration;
use crate::algorithms::learning::Learned;

/// Search diagnostics gathered by a solver for a `verbose` print
#[derive(Default)]
pub struct Stats {
    pub decisions: usize,
    // Calls of the closure: one per decision, per learned clause asserted,
    // and per set of assumptions
    pub propagations: usize,
    pub conflicts: usize,
    // How many learned clauses are stored, and how many have been deleted
    // in how many reductions of the database
    pub clauses: usize,
    pub reductions: usize,
    pub deleted: usize,
    pub restarts: usize,
    // The learned clauses: how long they are, how many literals
    // minimization took off them, and how many decision levels each jumped
    // back over -- chronological backtracking would always be exactly one
    learned_literals_sum: usize,
    learned_literals_max: usize,
    minimized_away_sum: usize,
    backjump_sum: usize,
    backjump_max: usize,
    nonchronological_backjumps: usize,
    // The learned clauses' literal block distances: their sum, and how
    // many fall in each of the bands 1-2, 3-5, 6-10 and above
    lbd_sum: usize,
    lbd_bands: [usize; 4],
    // Where the time goes: propagating (the closure rules and the learned
    // clauses together), analysing conflicts and minimizing their clauses,
    // choosing decisions, and backtracking
    pub propagating: Duration,
    pub analysing: Duration,
    pub deciding: Duration,
    pub backtracking: Duration,
    // How much the learned clauses cost propagation: clauses looked at
    // because a watched literal became false, and literals scanned while
    // looking for a new literal to watch
    pub clause_visits: usize,
    pub clause_literals_scanned: usize,
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
        self.lbd_sum += learned.lbd;
        let band = match learned.lbd {
            0..=2 => 0,
            3..=5 => 1,
            6..=10 => 2,
            _ => 3,
        };
        self.lbd_bands[band] += 1;
    }
}

impl Display for Stats {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let average = |sum: usize, count: usize| {
            if count > 0 { sum as f64 / count as f64 } else { 0.0 }
        };
        write!(
            f,
            "decisions={} propagations={} conflicts={} restarts={} clauses={} reductions={} deleted={} \
             learned_len_avg={:.1} learned_len_max={} \
             minimized_away_avg={:.1} backjump_avg={:.2} backjump_max={} nonchronological_backjumps={}",
            self.decisions,
            self.propagations,
            self.conflicts,
            self.restarts,
            self.clauses,
            self.reductions,
            self.deleted,
            average(self.learned_literals_sum, self.conflicts),
            self.learned_literals_max,
            average(self.minimized_away_sum, self.conflicts),
            average(self.backjump_sum, self.conflicts),
            self.backjump_max,
            self.nonchronological_backjumps,
        )?;
        write!(
            f,
            " lbd_avg={:.1} lbd_le2={} lbd_3to5={} lbd_6to10={} lbd_gt10={}",
            average(self.lbd_sum, self.conflicts),
            self.lbd_bands[0],
            self.lbd_bands[1],
            self.lbd_bands[2],
            self.lbd_bands[3],
        )?;
        let seconds = |d: Duration| d.as_secs_f64();
        write!(
            f,
            " propagating={:.1}s analysing={:.1}s deciding={:.1}s backtracking={:.1}s \
             clause_visits={} clause_literals_scanned={}",
            seconds(self.propagating),
            seconds(self.analysing),
            seconds(self.deciding),
            seconds(self.backtracking),
            self.clause_visits,
            self.clause_literals_scanned,
        )
    }
}
