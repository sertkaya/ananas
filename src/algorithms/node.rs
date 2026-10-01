use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use crate::af::AF;

/// Node of the search tree
#[derive(Debug, Clone)]
pub struct Node {
    // Whether an argument is part of this node's set of arguments,
    // indexed by argument id
    node_args: Vec<bool>,
    // Number of unattacked attackers for each argument
    unattacked_attackers_count: Vec<usize>,
    // Whether an argument has been ruled out of this node's set, indexed
    // by argument id. Together with node_args this is the search's partial
    // assignment: in, out, or still undecided. An argument lands here when
    // a candidate's whole subtree failed, and it is a hard constraint --
    // the closure must fail rather than force one of these back in.
    out: Vec<bool>,
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
    // Whether an argument's being defeated in every completion has already
    // been propagated to its own victims' undefeated_attackers_count
    known_defeated: Vec<bool>,
    // Number of each argument's attackers that could still be added to the
    // set, i.e. that are not ruled out, do not conflict with the set, and
    // do not attack themselves. For an undefeated attacker of the set this
    // is the number of ways left to defend the set against it: reaching 1
    // forces that defender, and reaching 0 kills the branch.
    usable_defenders_count: Vec<usize>,
    // Whether an argument has stopped being a usable defender, with that
    // fact already subtracted from its victims' usable_defenders_count
    defender_removed: Vec<bool>,
}

// Create a new node
impl Node {
    /// Create a new node from the initial attacker counts of an AF
    pub fn new(af: &AF) -> Node {
        let node_args = vec![false; af.argument_count()];
        let unattacked_attackers_count = (0..af.argument_count())
            .map(|a| af.attacker_count(a))
            .collect();
        let out = vec![false; af.argument_count()];
        let defeat_propagated = vec![false; af.argument_count()];
        let undefeated_attackers_count = (0..af.argument_count())
            .map(|a| af.attacker_count(a))
            .collect();
        let known_defeated = vec![false; af.argument_count()];
        // A self-attacking argument belongs to no conflict-free set, so it
        // is never a usable defender and is excluded from the counts here
        // rather than being subtracted later.
        let defender_removed: Vec<bool> = (0..af.argument_count())
            .map(|a| af.attacks(a, a))
            .collect();
        let usable_defenders_count = (0..af.argument_count())
            .map(|a| af.attackers(a).filter(|&&b| !defender_removed[b]).count())
            .collect();
        Node {
            node_args,
            unattacked_attackers_count,
            out,
            defeat_propagated,
            undefeated_attackers_count,
            known_defeated,
            usable_defenders_count,
            defender_removed,
        }
    }

    /// Add an argument to this node's set of arguments
    pub fn add_argument(&mut self, arg: usize) {
        self.node_args[arg] = true;
    }

    /// Check whether an argument is part of this node's set of arguments
    pub fn contains(&self, arg: usize) -> bool {
        self.node_args[arg]
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

    /// Check whether an argument has been ruled out of this node's set
    pub fn is_out(&self, arg: usize) -> bool {
        self.out[arg]
    }

    /// Rule an argument out of this node's set, and of every node derived
    /// from it. Used when a candidate's whole subtree has failed: it must
    /// never come back, not even as a side effect of some other
    /// candidate's closure.
    pub fn rule_out(&mut self, af: &AF, arg: usize) {
        self.out[arg] = true;
        self.remove_as_defender(af, arg);
    }

    /// Get the number of `arg`'s attackers that could still be added to the
    /// set -- for an undefeated attacker of the set, the number of ways
    /// left to defend against it
    pub fn usable_defenders_count(&self, arg: usize) -> usize {
        self.usable_defenders_count[arg]
    }

    /// Whether `arg` is still available to be added to the set as a defender
    pub fn is_usable_defender(&self, arg: usize) -> bool {
        !self.defender_removed[arg]
    }

    /// Record that `arg` can no longer be added to the set, subtracting it
    /// from the usable-defender count of every argument it attacks.
    /// Idempotent: an argument can stop being usable by being ruled out, by
    /// coming to conflict with the set, or both, and its victims' counts
    /// must only ever be decremented once for it.
    pub fn remove_as_defender(&mut self, af: &AF, arg: usize) {
        if self.defender_removed[arg] {
            return;
        }
        self.defender_removed[arg] = true;
        for &victim in af.victims(arg) {
            self.usable_defenders_count[victim] -= 1;
        }
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

    /// Check whether `arg`'s being defeated in every completion has already
    /// been propagated to its own victims. That `arg` is defeated is a
    /// one-time fact no matter how many ways it is established -- attacked
    /// by a member, attacking a member, or both -- so this must only ever
    /// happen once, or its victims' counts would be decremented twice for
    /// the same attacker.
    pub fn known_defeated(&self, arg: usize) -> bool {
        self.known_defeated[arg]
    }

    /// Mark `arg` as defeated in every completion, with that fact propagated
    pub fn mark_known_defeated(&mut self, arg: usize) {
        self.known_defeated[arg] = true;
    }

    /// Check whether `arg` conflicts with this node's set of arguments,
    /// i.e. `arg` attacks itself, `arg` attacks a member of the set, or a
    /// member of the set attacks `arg`
    pub fn conflicts_with(&self, af: &AF, arg: usize) -> bool {
        af.attacks(arg, arg)
            || af.victims(arg).any(|&v| self.contains(v))
            || self.is_defeated(af, arg)
    }

    /// Check whether every argument in this node's set is defended by the
    /// set itself, i.e. has no unattacked (undefeated) attackers left
    pub fn is_self_defending(&self) -> bool {
        self.node_args.iter().zip(&self.unattacked_attackers_count)
            .all(|(&in_set, &count)| !in_set || count == 0)
    }

    /// Collect the set of arguments currently in this node's set
    pub fn arguments(&self) -> HashSet<usize> {
        self.node_args.iter().enumerate()
            .filter_map(|(arg, &in_set)| in_set.then_some(arg))
            .collect()
    }
}

impl Display for Node {
    // Print the node
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "args: ")?;
        for (arg, &in_set) in self.node_args.iter().enumerate() {
            if in_set {
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