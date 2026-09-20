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
    // Whether an argument is prohibited from being added to node_args,
    // indexed by argument id
    prohibited: Vec<bool>,
    // Whether an argument's defeat has already been propagated to its own
    // victims' unattacked_attackers_count, indexed by argument id
    defeat_propagated: Vec<bool>,
}

// Create a new node
impl Node {
    /// Create a new node from the initial attacker counts of an AF
    pub fn new(af: &AF) -> Node {
        let node_args = vec![false; af.argument_count()];
        let unattacked_attackers_count = (0..af.argument_count())
            .map(|a| af.attacker_count(a))
            .collect();
        let prohibited = vec![false; af.argument_count()];
        let defeat_propagated = vec![false; af.argument_count()];
        Node {node_args, unattacked_attackers_count, prohibited, defeat_propagated}
    }

    /// Add an argument to this node's set of arguments
    pub fn add_argument(&mut self, arg: usize) {
        self.node_args[arg] = true;
        self.prohibit(arg);
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

    /// Check whether an argument is prohibited from being added to this
    /// node's set of arguments
    pub fn is_prohibited(&self, arg: usize) -> bool {
        self.prohibited[arg]
    }

    /// Prohibit an argument from being added to this node's set of arguments
    pub fn prohibit(&mut self, arg: usize) {
        self.prohibited[arg] = true;
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