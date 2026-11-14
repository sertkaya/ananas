//! Diagnostics about a search, printed in verbose mode.

use std::fmt::{Display, Formatter};
use crate::af::AF;
use crate::algorithms::closure::Conflict;
use crate::algorithms::learning::Analyzer;
use crate::algorithms::node::Node;

/// Search diagnostics gathered by a solver for a `verbose` print
#[derive(Default)]
pub struct Stats {
    pub nodes_visited: usize,
    pub pseudo_complete_calls: usize,
    // Distribution of candidates.len() at every frame creation (root and
    // children), to see whether difficulty comes from many nodes each
    // having a handful of candidates, or a few nodes with huge candidate
    // lists.
    frames_created: usize,
    candidate_count_sum: usize,
    candidate_count_min: Option<usize>,
    candidate_count_max: usize,
    // How often candidates() came back empty: the branch was already dead,
    // but pseudo_complete did not notice, so we paid a full candidate scan
    // to find out.
    empty_candidate_lists: usize,
    // What conflict learning would make of the search's conflicts: how
    // many there are, how long the clauses learned from them are, and how
    // many decision levels each would jump back over -- where the search
    // itself always backtracks exactly one.
    conflicts: usize,
    learned_literals_sum: usize,
    learned_literals_max: usize,
    minimized_away_sum: usize,
    backjump_sum: usize,
    backjump_max: usize,
    nonchronological_backjumps: usize,
}

impl Stats {
    /// Record a frame created with `candidates` to try
    pub fn record_frame(&mut self, candidates: &[usize]) {
        self.frames_created += 1;
        self.candidate_count_sum += candidates.len();
        self.candidate_count_max = self.candidate_count_max.max(candidates.len());
        self.candidate_count_min = Some(
            self.candidate_count_min.map_or(candidates.len(), |m| m.min(candidates.len())),
        );
        if candidates.is_empty() {
            self.empty_candidate_lists += 1;
        }
    }

    /// Analyse `conflict`, just run into on `node`, and record the clause
    /// learning would make of it
    pub fn record_conflict(&mut self, conflict: Conflict, node: &Node, af: &AF, analyzer: &mut Analyzer) {
        let Some(learned) = analyzer.analyze(conflict, node, af) else {
            return;
        };
        let jump = node.decision_level() - learned.assertion_level;
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
            "nodes_visited={} pseudo_complete_calls={} frames_created={} \
             candidates_avg={:.2} candidates_min={} candidates_max={} \
             empty_candidate_lists={}",
            self.nodes_visited,
            self.pseudo_complete_calls,
            self.frames_created,
            average(self.candidate_count_sum, self.frames_created),
            self.candidate_count_min.unwrap_or(0),
            self.candidate_count_max,
            self.empty_candidate_lists,
        )?;
        if self.conflicts > 0 {
            write!(
                f,
                " conflicts={} learned_len_avg={:.1} learned_len_max={} minimized_away_avg={:.1} \
                 backjump_avg={:.2} backjump_max={} nonchronological_backjumps={}",
                self.conflicts,
                average(self.learned_literals_sum, self.conflicts),
                self.learned_literals_max,
                average(self.minimized_away_sum, self.conflicts),
                average(self.backjump_sum, self.conflicts),
                self.backjump_max,
                self.nonchronological_backjumps,
            )?;
        }
        Ok(())
    }
}
