use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use crate::af::AF;

/// Whether an argument belongs to a node's set: decided either way, or not
/// yet decided
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    Undecided,
    In,
    Out,
}

/// Why an argument was assigned its value. Recorded with every assignment
/// so that a conflict can later be traced back to the assignments that
/// caused it.
///
/// Only the rule is recorded, not the arguments it fired on: the node is
/// cloned for every search step, so it stays one byte per argument. The
/// antecedents are cheap to recover from the framework when a conflict
/// needs explaining, which is rare by comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Reason {
    /// In by assumption: the query argument, an unattacked argument, or a
    /// search decision
    Decision,
    /// Out because it attacks itself
    SelfAttack,
    /// Out because a search candidate's whole subtree failed with it in
    RuledOut,
    /// Out because it attacks, or is attacked by, a member
    Member,
    /// In because every one of its attackers is known defeated
    Completeness,
    /// In because it is the only usable defender left against an argument
    /// it attacks, which must be defeated
    OnlyDefender,
}

/// A fact assigned during propagation, whose consequences are still to be
/// propagated
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lit {
    /// The argument is in the set
    In(usize),
    /// The argument is out of the set
    Out(usize),
    /// The argument is defeated in every complete extension of the set
    Def(usize),
}

/// Outcome of assigning a value to an argument
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assignment {
    /// The argument was undecided and now has the value
    New,
    /// The argument already had the value
    Unchanged,
    /// The argument already had the opposite value
    Conflict,
}

/// Node of the search tree
#[derive(Debug, Clone)]
pub struct Node {
    // The search's partial assignment: whether each argument is in the
    // node's set, out of it, or still undecided, indexed by argument id.
    // An argument is out when it conflicts with the set, attacks itself, or
    // was ruled out because a candidate's whole subtree failed; the closure
    // must fail rather than force an out argument back in.
    value: Vec<Value>,
    // Why each decided argument got its value. Meaningless for undecided
    // arguments.
    reason: Vec<Reason>,
    // Number of unattacked attackers for each argument
    unattacked_attackers_count: Vec<usize>,
    // Whether an argument's defeat has already been propagated to its own
    // victims' unattacked_attackers_count, indexed by argument id
    defeat_propagated: Vec<bool>,
    // Number of attackers of each argument not yet known to be defeated in
    // every completion of this node's set. An attacker counts as known
    // defeated either because a member of the set attacks it, or because it
    // attacks a member (a complete extension must defend its members, so it
    // must attack back). Reaching 0 means every attacker of the argument is
    // defeated in any completion, so the argument is defended and must be in.
    undefeated_attackers_count: Vec<usize>,
    // Whether an argument is known to be defeated in every completion of
    // this node's set, with that fact queued for propagation to its own
    // victims' undefeated_attackers_count
    known_defeated: Vec<bool>,
    // Number of each argument's attackers whose being out has not yet been
    // propagated. Never less than the number of attackers that could still
    // be added, so for an undefeated attacker of the set it bounds the ways
    // left to defend against it: reaching 1 may force that defender, and
    // reaching 0 kills the branch.
    usable_defenders_count: Vec<usize>,
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
        let unattacked_attackers_count = (0..af.argument_count())
            .map(|a| af.attacker_count(a))
            .collect();
        let defeat_propagated = vec![false; af.argument_count()];
        let undefeated_attackers_count = (0..af.argument_count())
            .map(|a| af.attacker_count(a))
            .collect();
        let known_defeated = vec![false; af.argument_count()];
        let usable_defenders_count = (0..af.argument_count())
            .map(|a| af.attackers(a).filter(|&&b| !self_attacking[b]).count())
            .collect();
        Node {
            value,
            reason,
            unattacked_attackers_count,
            defeat_propagated,
            undefeated_attackers_count,
            known_defeated,
            usable_defenders_count,
        }
    }

    /// Get the value of an argument
    pub fn value(&self, arg: usize) -> Value {
        self.value[arg]
    }

    /// Get why a decided argument got its value
    // Not read outside tests until conflict analysis lands
    #[allow(dead_code)]
    pub fn reason(&self, arg: usize) -> Reason {
        self.reason[arg]
    }

    /// Assign a value, `Value::In` or `Value::Out`, to an argument, for the
    /// given reason. A conflict leaves the node unchanged.
    pub fn assign(&mut self, arg: usize, value: Value, reason: Reason) -> Assignment {
        debug_assert!(value != Value::Undecided);
        if self.value[arg] == value {
            Assignment::Unchanged
        } else if self.value[arg] != Value::Undecided {
            Assignment::Conflict
        } else {
            self.value[arg] = value;
            self.reason[arg] = reason;
            Assignment::New
        }
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

    /// Decrement the number of unattacked attackers of an argument and
    /// return the new count
    pub fn decrement_unattacked_attackers(&mut self, arg: usize) -> usize {
        self.unattacked_attackers_count[arg] -= 1;
        self.unattacked_attackers_count[arg]
    }

    /// Get the bound on the number of `arg`'s attackers that could still
    /// be added to the set -- for an undefeated attacker of the set, the
    /// number of ways left to defend against it
    pub fn usable_defenders_count(&self, arg: usize) -> usize {
        self.usable_defenders_count[arg]
    }

    /// Decrement the usable-defender count of an argument and return the
    /// new count
    pub fn decrement_usable_defenders(&mut self, arg: usize) -> usize {
        self.usable_defenders_count[arg] -= 1;
        self.usable_defenders_count[arg]
    }

    /// Check whether `arg` is attacked by any argument already in this
    /// node's set
    pub fn is_defeated(&self, af: &AF, arg: usize) -> bool {
        af.attackers(arg).any(|&a| self.contains(a))
    }

    /// Check whether `arg`'s defeat has already been propagated to its own
    /// victims' unattacked_attackers_count. `arg` being defeated is a
    /// one-time fact regardless of how many of its attackers are accepted,
    /// so this must only ever happen once.
    pub fn defeat_propagated(&self, arg: usize) -> bool {
        self.defeat_propagated[arg]
    }

    /// Mark `arg`'s defeat as having been propagated
    pub fn mark_defeat_propagated(&mut self, arg: usize) {
        self.defeat_propagated[arg] = true;
    }

    /// Decrement the number of `arg`'s attackers not yet known to be
    /// defeated in every completion, and return the new count
    pub fn decrement_undefeated_attackers(&mut self, arg: usize) -> usize {
        self.undefeated_attackers_count[arg] -= 1;
        self.undefeated_attackers_count[arg]
    }

    /// Check whether `arg` is known to be defeated in every completion.
    /// That `arg` is defeated is a one-time fact no matter how many ways it
    /// is established -- attacked by a member, attacking a member, or both
    /// -- so it is recorded, and propagated to its victims, only once.
    pub fn known_defeated(&self, arg: usize) -> bool {
        self.known_defeated[arg]
    }

    /// Record that `arg` is defeated in every completion. Returns `false`,
    /// leaving the node unchanged, if it was already known.
    pub fn assign_def(&mut self, arg: usize) -> bool {
        if self.known_defeated[arg] {
            return false;
        }
        self.known_defeated[arg] = true;
        true
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
