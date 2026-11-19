//! Activity of arguments: how much each has been involved in recent
//! conflicts, for choosing decisions that stay close to where the search
//! is learning. The scheme of MiniSat's VSIDS: every argument that
//! conflict analysis resolves through is bumped by an increment that grows
//! after each conflict, so that older involvement decays geometrically
//! relative to newer.
//!
//! The arguments are also kept in a heap, most active first, so that the
//! search finds its next decision without scanning every argument. They
//! can be put in groups, a smaller group coming first regardless of
//! activity, for a decision order that activity only refines. The
//! heap holds at least every undecided argument; the search drops decided
//! ones as it pops them and puts arguments back as backtracking undecides
//! them.

/// Per-argument activity scores, and a heap of arguments by activity
pub struct Activity {
    score: Vec<f64>,
    // What one bump currently adds; grows by 1/DECAY per conflict
    increment: f64,
    // Among equally active arguments, the one with the smaller rank first
    rank: Vec<usize>,
    // Ahead of activity, the argument in the smaller group first
    group: Vec<usize>,
    // A binary max-heap of arguments, and each argument's index in it
    heap: Vec<usize>,
    position: Vec<Option<usize>>,
}

// The share an argument's activity keeps per conflict, relative to the
// current increment
const DECAY: f64 = 0.95;
// Scores are rescaled by this when the increment outgrows it
const RESCALE: f64 = 1e100;

impl Activity {
    /// No involvement yet, for the arguments in `order`, all in the heap.
    /// Equally active arguments come out of the heap in that order, which
    /// must hold every argument once.
    pub fn new(order: Vec<usize>) -> Activity {
        let mut rank = vec![0; order.len()];
        let mut position = vec![None; order.len()];
        for (i, &a) in order.iter().enumerate() {
            rank[a] = i;
            position[a] = Some(i);
        }
        // Sorted by rank, and all equally (in)active, it already is a heap
        let group = vec![0; order.len()];
        Activity { score: vec![0.0; order.len()], increment: 1.0, rank, group, heap: order, position }
    }

    /// Put every argument `a` in group `group[a]`: the heap hands out the
    /// smaller groups first, by activity within a group
    pub fn set_groups(&mut self, group: Vec<usize>) {
        self.group = group;
        self.rebuild();
    }

    /// The group of `arg`, 0 unless set
    pub fn group(&self, arg: usize) -> usize {
        self.group[arg]
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
            // Rounding may have made distinct scores equal, which the
            // ranks then order differently
            self.rebuild();
        } else if let Some(i) = self.position[arg] {
            self.up(i);
        }
    }

    /// Let every activity so far decay relative to the next bumps, once per
    /// conflict
    pub fn decay(&mut self) {
        self.increment /= DECAY;
    }

    /// Put `arg` in the heap, if it is not there already
    pub fn insert(&mut self, arg: usize) {
        if self.position[arg].is_none() {
            self.position[arg] = Some(self.heap.len());
            self.heap.push(arg);
            self.up(self.heap.len() - 1);
        }
    }

    /// Take the most active argument out of the heap
    pub fn pop(&mut self) -> Option<usize> {
        let top = *self.heap.first()?;
        let last = self.heap.pop().expect("the heap is not empty");
        self.position[top] = None;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.position[last] = Some(0);
            self.down(0);
        }
        Some(top)
    }

    /// Whether `a` comes out of the heap before `b`
    fn before(&self, a: usize, b: usize) -> bool {
        if self.group[a] != self.group[b] {
            return self.group[a] < self.group[b];
        }
        let (x, y) = (self.score[a], self.score[b]);
        x > y || (x == y && self.rank[a] < self.rank[b])
    }

    fn up(&mut self, mut i: usize) {
        let a = self.heap[i];
        while i > 0 {
            let parent = (i - 1) / 2;
            let p = self.heap[parent];
            if !self.before(a, p) {
                break;
            }
            self.heap[i] = p;
            self.position[p] = Some(i);
            i = parent;
        }
        self.heap[i] = a;
        self.position[a] = Some(i);
    }

    fn down(&mut self, mut i: usize) {
        let a = self.heap[i];
        loop {
            let left = 2 * i + 1;
            if left >= self.heap.len() {
                break;
            }
            let right = left + 1;
            let child = if right < self.heap.len() && self.before(self.heap[right], self.heap[left]) {
                right
            } else {
                left
            };
            let c = self.heap[child];
            if !self.before(c, a) {
                break;
            }
            self.heap[i] = c;
            self.position[c] = Some(i);
            i = child;
        }
        self.heap[i] = a;
        self.position[a] = Some(i);
    }

    fn rebuild(&mut self) {
        for i in (0..self.heap.len() / 2).rev() {
            self.down(i);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::random_af::Rng;

    // Whatever the bumps, insertions and pops, the heap hands out its
    // arguments by group, most active first within one, equals by rank.
    #[test]
    fn test_heap_pops_by_group_activity_then_rank() {
        let mut rng = Rng::new(3);
        for _ in 0..200 {
            let n = 1 + rng.below(30);
            let mut order: Vec<usize> = (0..n).collect();
            for i in (1..n).rev() {
                order.swap(i, rng.below(i + 1));
            }
            let mut rank = vec![0; n];
            for (i, &a) in order.iter().enumerate() {
                rank[a] = i;
            }
            let mut activity = Activity::new(order);
            // Half the time in a few groups, set before or during the run
            let groups = rng.below(2) == 1;
            let group: Vec<usize> = (0..n).map(|_| if groups { rng.below(4) } else { 0 }).collect();
            if groups {
                activity.set_groups(group.clone());
            }
            let mut out = Vec::new();
            for _ in 0..100 {
                match rng.below(4) {
                    0 => activity.bump(rng.below(n)),
                    1 => activity.decay(),
                    2 => {
                        if let Some(a) = activity.pop() {
                            out.push(a);
                        }
                    }
                    _ => {
                        if let Some(a) = out.pop() {
                            activity.insert(a);
                        }
                    }
                }
            }
            let mut popped = Vec::new();
            while let Some(a) = activity.pop() {
                popped.push(a);
            }
            let mut expected = popped.clone();
            expected.sort_by(|&a, &b| {
                group[a].cmp(&group[b])
                    .then(activity.of(b).total_cmp(&activity.of(a)))
                    .then(rank[a].cmp(&rank[b]))
            });
            assert_eq!(popped, expected);
        }
    }

    // Many conflicts' worth of decays push the scores past RESCALE
    // several times; the heap order survives the rescaling.
    #[test]
    fn test_heap_survives_rescaling() {
        let mut rng = Rng::new(4);
        let n = 20;
        let mut activity = Activity::new((0..n).rev().collect());
        for _ in 0..20000 {
            activity.bump(rng.below(n));
            activity.decay();
        }
        let mut popped = Vec::new();
        while let Some(a) = activity.pop() {
            popped.push(a);
        }
        assert_eq!(popped.len(), n);
        assert!(popped.windows(2).all(|w| activity.of(w[0]) >= activity.of(w[1])));
    }
}
