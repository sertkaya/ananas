//! Activity of arguments: how much each has been involved in recent
//! conflicts, for choosing decisions that stay close to where the search
//! is learning. The scheme of MiniSat's VSIDS: every argument that
//! conflict analysis resolves through is bumped by an increment that grows
//! after each conflict, so that older involvement decays geometrically
//! relative to newer.

/// Per-argument activity scores
pub struct Activity {
    score: Vec<f64>,
    // What one bump currently adds; grows by 1/DECAY per conflict
    increment: f64,
}

// The share an argument's activity keeps per conflict, relative to the
// current increment
const DECAY: f64 = 0.95;
// Scores are rescaled by this when the increment outgrows it
const RESCALE: f64 = 1e100;

impl Activity {
    /// No involvement yet, for `argument_count` arguments
    pub fn new(argument_count: usize) -> Activity {
        Activity { score: vec![0.0; argument_count], increment: 1.0 }
    }

    /// The activity of `arg`
    pub fn of(&self, arg: usize) -> f64 {
        self.score[arg]
    }

    /// Record `arg`'s involvement in the conflict being analysed
    pub fn bump(&mut self, arg: usize) {
        self.score[arg] += self.increment;
        if self.score[arg] > RESCALE {
            for score in &mut self.score {
                *score /= RESCALE;
            }
            self.increment /= RESCALE;
        }
    }

    /// Let every activity so far decay relative to the next bumps, once per
    /// conflict
    pub fn decay(&mut self) {
        self.increment /= DECAY;
    }
}
