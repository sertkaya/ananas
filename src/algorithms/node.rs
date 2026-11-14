use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use crate::af::AF;
use crate::algorithms::clauses::ClauseDb;
use crate::algorithms::lit::{Assignment, Lit, Reason, Value};

/// The search's state: a partial assignment, the trail of assignments that
/// built it, and the counters the closure rules derive from it.
///
/// There is one node per search, not one per search-tree node. Going deeper
/// appends to the trail; backtracking pops the trail and reverses each
/// popped assignment, so a search step costs the work it does rather than a
/// copy of the whole state.
#[derive(Debug, Clone)]
pub struct Node {
    // The search's partial assignment: whether each argument is in the
    // node's set, out of it, or still undecided, indexed by argument id.
    // An argument is out when it conflicts with the set, attacks itself, or
    // was ruled out because a candidate's whole subtree failed; the closure
    // must fail rather than force an out argument back in.
    value: Vec<Value>,
    // Why each decided argument got its value, and at which decision level.
    // Meaningless for undecided arguments.
    reason: Vec<Reason>,
    level: Vec<usize>,
    // Number of unattacked attackers for each argument
    unattacked_attackers_count: Vec<usize>,
    // Number of each argument's attackers whose being in has been
    // propagated. Its going from 0 to 1 is the argument's defeat, which is
    // what is propagated to its victims' unattacked_attackers_count; kept as
    // a count rather than a flag so that undoing it is symmetric.
    in_attackers_count: Vec<usize>,
    // Number of attackers of each argument not yet known to be defeated in
    // every completion of this node's set. An attacker counts as known
    // defeated either because a member of the set attacks it, or because it
    // attacks a member (a complete extension must defend its members, so it
    // must attack back). Reaching 0 means every attacker of the argument is
    // defeated in any completion, so the argument is defended and must be in.
    undefeated_attackers_count: Vec<usize>,
    // Whether an argument is known to be defeated in every completion of
    // this node's set, with that fact on the trail for propagation to its
    // own victims' undefeated_attackers_count
    known_defeated: Vec<bool>,
    // For each argument known defeated, the member that established it:
    // one the argument attacks or is attacked by. Meaningless otherwise.
    def_source: Vec<usize>,
    // Number of each argument's attackers whose being out has not yet been
    // propagated. Never less than the number of attackers that could still
    // be added, so for an undefeated attacker of the set it bounds the ways
    // left to defend against it: reaching 1 may force that defender, and
    // reaching 0 kills the branch.
    usable_defenders_count: Vec<usize>,
    // Every assignment, in the order it was made. The self-attackers are
    // out from the start and are not on it.
    trail: Vec<Lit>,
    // How many assignments at the front of the trail have had their
    // consequences propagated; the rest are still queued.
    propagated: usize,
    // The trail's length when each decision level above 0 began, so the
    // current decision level is the length of this
    level_start: Vec<usize>,
    // The clauses learned so far, with their watches
    clauses: ClauseDb,
}

// Create a new node
impl Node {
    /// Create a new node from the initial attacker counts of an AF
    pub fn new(af: &AF) -> Node {
        // A self-attacking argument belongs to no conflict-free set, so it
        // starts out, and is excluded from the usable-defender counts here
        // rather than being propagated later.
        let self_attacking: Vec<bool> = (0..af.argument_count())
            .map(|a| af.attacks(a, a))
            .collect();
        let value = self_attacking.iter()
            .map(|&s| if s { Value::Out } else { Value::Undecided })
            .collect();
        let reason = vec![Reason::SelfAttack; af.argument_count()];
        let level = vec![0; af.argument_count()];
        let unattacked_attackers_count = (0..af.argument_count())
            .map(|a| af.attacker_count(a))
            .collect();
        let in_attackers_count = vec![0; af.argument_count()];
        let undefeated_attackers_count = (0..af.argument_count())
            .map(|a| af.attacker_count(a))
            .collect();
        let known_defeated = vec![false; af.argument_count()];
        let def_source = vec![0; af.argument_count()];
        let usable_defenders_count = (0..af.argument_count())
            .map(|a| af.attackers(a).filter(|&&b| !self_attacking[b]).count())
            .collect();
        Node {
            value,
            reason,
            level,
            unattacked_attackers_count,
            in_attackers_count,
            undefeated_attackers_count,
            known_defeated,
            def_source,
            usable_defenders_count,
            trail: Vec::new(),
            propagated: 0,
            level_start: Vec::new(),
            clauses: ClauseDb::new(af.argument_count()),
        }
    }

    /// Whether a literal is true or false under the assignment, or `None`
    /// while it is not decided
    pub fn lit_value(&self, lit: Lit) -> Option<bool> {
        match lit {
            Lit::In(a) => match self.value[a] {
                Value::In => Some(true),
                Value::Out => Some(false),
                Value::Undecided => None,
            },
            Lit::Out(a) => match self.value[a] {
                Value::Out => Some(true),
                Value::In => Some(false),
                Value::Undecided => None,
            },
            Lit::Def(a) => self.known_defeated[a].then_some(true),
        }
    }

    /// The learned clauses and their watches
    pub fn clauses(&self) -> &ClauseDb {
        &self.clauses
    }

    /// The learned clauses and their watches, to add to or rewatch
    pub fn clauses_mut(&mut self) -> &mut ClauseDb {
        &mut self.clauses
    }

    /// Get the number of arguments
    #[cfg(test)]
    pub fn value_count(&self) -> usize {
        self.value.len()
    }

    /// Get the value of an argument
    pub fn value(&self, arg: usize) -> Value {
        self.value[arg]
    }

    /// Get why a decided argument got its value
    pub fn reason(&self, arg: usize) -> Reason {
        self.reason[arg]
    }

    /// Get the decision level at which a decided argument got its value
    pub fn level(&self, arg: usize) -> usize {
        self.level[arg]
    }

    /// Get the current decision level: 0 until the first decision
    pub fn decision_level(&self) -> usize {
        self.level_start.len()
    }

    /// Begin a new decision level, above the current one
    pub fn new_level(&mut self) {
        self.level_start.push(self.trail.len());
    }

    /// Drop every decision level above `level`, returning the length the
    /// trail had when the first of them began -- what to backtrack it to
    pub fn drop_levels_above(&mut self, level: usize) -> usize {
        let len = self.level_start[level];
        self.level_start.truncate(level);
        len
    }

    /// Get every assignment made so far, in order
    pub fn trail(&self) -> &[Lit] {
        &self.trail
    }

    /// Assign a value, `Value::In` or `Value::Out`, to an argument, for the
    /// given reason, appending it to the trail if it is new. A conflict
    /// leaves the node unchanged.
    pub fn assign(&mut self, arg: usize, value: Value, reason: Reason) -> Assignment {
        debug_assert!(value != Value::Undecided);
        if self.value[arg] == value {
            Assignment::Unchanged
        } else if self.value[arg] != Value::Undecided {
            Assignment::Conflict
        } else {
            self.value[arg] = value;
            self.reason[arg] = reason;
            self.level[arg] = self.level_start.len();
            self.trail.push(match value {
                Value::In => Lit::In(arg),
                _ => Lit::Out(arg),
            });
            Assignment::New
        }
    }

    /// Take the next assignment whose consequences are still to be
    /// propagated, counting it as propagated from now on
    pub fn next_to_propagate(&mut self) -> Option<Lit> {
        let lit = *self.trail.get(self.propagated)?;
        self.propagated += 1;
        Some(lit)
    }

    /// Undo the latest assignment, if the trail is longer than `len`.
    /// Returns it, and whether it had been propagated -- if so, the caller
    /// must reverse what propagating it did to the counters.
    pub fn unassign_last(&mut self, len: usize) -> Option<(Lit, bool)> {
        if self.trail.len() <= len {
            return None;
        }
        let lit = self.trail.pop().expect("the trail is longer than len");
        let was_propagated = self.trail.len() < self.propagated;
        if was_propagated {
            self.propagated = self.trail.len();
        }
        match lit {
            Lit::In(a) | Lit::Out(a) => self.value[a] = Value::Undecided,
            Lit::Def(a) => self.known_defeated[a] = false,
        }
        Some((lit, was_propagated))
    }

    /// Check whether an argument is part of this node's set of arguments
    pub fn contains(&self, arg: usize) -> bool {
        self.value[arg] == Value::In
    }

    /// Check whether an argument has been ruled out of this node's set
    pub fn is_out(&self, arg: usize) -> bool {
        self.value[arg] == Value::Out
    }

    /// Get the number of unattacked (undefeated) attackers of an argument
    pub fn unattacked_attackers_count(&self, arg: usize) -> usize {
        self.unattacked_attackers_count[arg]
    }

    /// Decrement the number of unattacked attackers of an argument
    pub fn decrement_unattacked_attackers(&mut self, arg: usize) {
        self.unattacked_attackers_count[arg] -= 1;
    }

    /// Increment the number of unattacked attackers of an argument
    pub fn increment_unattacked_attackers(&mut self, arg: usize) {
        self.unattacked_attackers_count[arg] += 1;
    }

    /// Get the bound on the number of `arg`'s attackers that could still
    /// be added to the set -- for an undefeated attacker of the set, the
    /// number of ways left to defend against it
    pub fn usable_defenders_count(&self, arg: usize) -> usize {
        self.usable_defenders_count[arg]
    }

    /// Decrement the usable-defender count of an argument
    pub fn decrement_usable_defenders(&mut self, arg: usize) {
        self.usable_defenders_count[arg] -= 1;
    }

    /// Increment the usable-defender count of an argument
    pub fn increment_usable_defenders(&mut self, arg: usize) {
        self.usable_defenders_count[arg] += 1;
    }

    /// Check whether `arg` is attacked by any argument already in this
    /// node's set
    pub fn is_defeated(&self, af: &AF, arg: usize) -> bool {
        af.attackers(arg).any(|&a| self.contains(a))
    }

    /// Check whether `arg`'s defeat has already been propagated to its own
    /// victims' unattacked_attackers_count. `arg` being defeated is a
    /// one-time fact regardless of how many of its attackers are accepted,
    /// so it is propagated with the first of them and undone with the last.
    pub fn defeat_propagated(&self, arg: usize) -> bool {
        self.in_attackers_count[arg] > 0
    }

    /// Count one more of `arg`'s attackers as propagated in, and return
    /// whether it is the first -- i.e. whether `arg`'s defeat is new
    pub fn add_in_attacker(&mut self, arg: usize) -> bool {
        self.in_attackers_count[arg] += 1;
        self.in_attackers_count[arg] == 1
    }

    /// Count one fewer of `arg`'s attackers as propagated in, and return
    /// whether it was the last -- i.e. whether `arg`'s defeat is undone
    pub fn remove_in_attacker(&mut self, arg: usize) -> bool {
        self.in_attackers_count[arg] -= 1;
        self.in_attackers_count[arg] == 0
    }

    /// Get the number of `arg`'s attackers not yet known to be defeated in
    /// every completion
    pub fn undefeated_attackers_count(&self, arg: usize) -> usize {
        self.undefeated_attackers_count[arg]
    }

    /// Decrement the number of `arg`'s attackers not yet known to be
    /// defeated in every completion
    pub fn decrement_undefeated_attackers(&mut self, arg: usize) {
        self.undefeated_attackers_count[arg] -= 1;
    }

    /// Increment the number of `arg`'s attackers not yet known to be
    /// defeated in every completion
    pub fn increment_undefeated_attackers(&mut self, arg: usize) {
        self.undefeated_attackers_count[arg] += 1;
    }

    /// Check whether `arg` is known to be defeated in every completion.
    /// That `arg` is defeated is a one-time fact no matter how many ways it
    /// is established -- attacked by a member, attacking a member, or both
    /// -- so it is recorded, and propagated to its victims, only once.
    pub fn known_defeated(&self, arg: usize) -> bool {
        self.known_defeated[arg]
    }

    /// Get the member that established `arg` as defeated in every
    /// completion. Meaningless unless `arg` is known defeated.
    pub fn def_source(&self, arg: usize) -> usize {
        self.def_source[arg]
    }

    /// Record that `arg` is defeated in every completion because of
    /// `member`, appending it to the trail. Does nothing if it was already
    /// known.
    pub fn assign_def(&mut self, arg: usize, member: usize) {
        if !self.known_defeated[arg] {
            self.known_defeated[arg] = true;
            self.def_source[arg] = member;
            self.trail.push(Lit::Def(arg));
        }
    }

    /// Check whether every argument in this node's set is defended by the
    /// set itself, i.e. has no unattacked (undefeated) attackers left
    pub fn is_self_defending(&self) -> bool {
        self.value.iter().zip(&self.unattacked_attackers_count)
            .all(|(&value, &count)| value != Value::In || count == 0)
    }

    /// Collect the set of arguments currently in this node's set
    pub fn arguments(&self) -> HashSet<usize> {
        self.value.iter().enumerate()
            .filter_map(|(arg, &value)| (value == Value::In).then_some(arg))
            .collect()
    }
}

#[cfg(test)]
impl Node {
    /// Assert that this node is in exactly the state `other` is in, apart
    /// from stale entries for undecided arguments, which mean nothing
    pub fn assert_same_state(&self, other: &Node) {
        assert_eq!(self.value, other.value, "values differ");
        for (a, &value) in self.value.iter().enumerate() {
            if value != Value::Undecided {
                assert_eq!(self.reason[a], other.reason[a], "reasons of {a} differ");
                assert_eq!(self.level[a], other.level[a], "levels of {a} differ");
            }
            if self.known_defeated[a] {
                assert_eq!(self.def_source[a], other.def_source[a], "def sources of {a} differ");
            }
        }
        assert_eq!(self.unattacked_attackers_count, other.unattacked_attackers_count);
        assert_eq!(self.in_attackers_count, other.in_attackers_count);
        assert_eq!(self.undefeated_attackers_count, other.undefeated_attackers_count);
        assert_eq!(self.known_defeated, other.known_defeated);
        assert_eq!(self.usable_defenders_count, other.usable_defenders_count);
        assert_eq!(self.trail, other.trail);
        assert_eq!(self.propagated, other.propagated);
        assert_eq!(self.level_start, other.level_start);
    }
}

impl Display for Node {
    // Print the node
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "args: ")?;
        for (arg, &value) in self.value.iter().enumerate() {
            if value == Value::In {
                write!(f, "{} ", arg)?;
            }
        }
        writeln!(f)?;
        for (index, count) in self.unattacked_attackers_count.iter().enumerate() {
            write!(f, "{}: ", index)?;
            write!(f, "{} ", count)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use crate::io::af_parser::read_af;
    use super::*;

    #[test]
    fn test_new_node() -> std::io::Result<()> {
        let input_af = File::open("tests/jelia23-example.af")?;
        let af = read_af(input_af);
        println!("{}", af);
        let node = Node::new(&af);
        println!("{}", node);
        Ok(())
    }
}
