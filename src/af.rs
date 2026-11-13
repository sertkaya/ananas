use std::collections::HashSet;
use std::slice::Iter;
use std::fmt::{Display, Formatter};

/// Argumentation framework represented as adjacency list.
#[derive(Debug)]
pub struct AF {
    // Number of arguments
    arg_count: usize,
    // Adjacency list for attacks relation: for each argument, the
    // arguments it attacks, sorted ascending and without duplicates.
    // Sorted rather than hashed so that iteration order is a property of
    // the framework, not of the per-process hash seed -- the search's
    // propagation order, and so the work it does, must be reproducible.
    attacks: Vec<Vec<usize>>,
    // Adjacency list for attacked-by relation, kept the same way
    attacked_by: Vec<Vec<usize>>,
}

impl Display for AF {
    // Print the argumentation framework
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (index, list) in self.attacks.iter().enumerate() {
            write!(f, "{}: ", index)?;
            for arg in list  {
               write!(f, "{} ", arg)?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl AF {
    /// Create a new argumentation framework with the given number of arguments
    pub fn new(size: usize) -> AF {
        let attacks: Vec<Vec<usize>> = vec![Vec::new(); size];
        let attacked_by: Vec<Vec<usize>> = vec![Vec::new(); size];
        AF { arg_count: size, attacks, attacked_by }
    }

    /// Add an attack from the attacker to the victim. Adding an attack
    /// that is already present has no effect.
    pub fn add_attack(&mut self, attacker: usize, victim: usize) {
        // add the attack to the attacks relation
        if insert_sorted(&mut self.attacks[attacker], victim) {
            // add the attack to the attacked-by relation
            insert_sorted(&mut self.attacked_by[victim], attacker);
        }
    }

    /// Get the number of arguments
    pub fn argument_count(&self) -> usize { self.arg_count }

    /// Get the number of attacks
    pub fn attack_count(&self) ->usize  {
        self.attacks.iter().map(|s| s.len()).sum()
    }

    /// Get the victims of an argument
    pub fn victims(&self, arg: usize) -> Iter<'_, usize> {
        self.attacks[arg].iter()
    }

    /// Get the number of attackers of an argument
    pub fn attacker_count(&self, a: usize) -> usize {
        self.attacked_by[a].len()
    }

    /// Get the attackers of an argument
    pub fn attackers(&self, arg: usize) -> Iter<'_, usize> {
        self.attacked_by[arg].iter()
    }

    /// Check if argument a attacks argument b
    pub fn attacks(&self, a: usize, b: usize) -> bool {
        self.attacks[a].binary_search(&b).is_ok()
    }

    /// Check if argument a attacks any argument in the set s
    pub fn attacks_set(&self, a: usize, s: &HashSet<usize>) -> bool {
        self.attacks[a].iter().any(|v| s.contains(v))
    }

    /// Check if argument a is attacked by any argument in the set s
    pub fn attacked_by_set(&self, a: usize, s: &HashSet<usize>) -> bool {
        self.attacked_by[a].iter().any(|b| s.contains(b))
    }

    /// Check whether `set` defends `arg`: every attacker of `arg` is
    /// itself attacked by some member of `set`
    fn defends(&self, set: &HashSet<usize>, arg: usize) -> bool {
        self.attackers(arg).all(|&b| self.attacked_by_set(b, set))
    }

    /// Check whether `set` is conflict-free: no member attacks another
    pub fn is_conflict_free(&self, set: &HashSet<usize>) -> bool {
        set.iter().all(|&a| !self.attacks_set(a, set))
    }

    /// Check whether `set` is admissible: conflict-free, and defends all
    /// of its own members
    pub fn is_admissible(&self, set: &HashSet<usize>) -> bool {
        self.is_conflict_free(set) && set.iter().all(|&a| self.defends(set, a))
    }

    /// Check whether `set` is a complete extension: admissible, and
    /// contains every argument it defends
    pub fn is_complete(&self, set: &HashSet<usize>) -> bool {
        self.is_admissible(set)
            && (0..self.arg_count).all(|a| set.contains(&a) || !self.defends(set, a))
    }

    /// Check whether `set` is a stable extension: conflict-free, and
    /// attacks every argument outside itself
    pub fn is_stable(&self, set: &HashSet<usize>) -> bool {
        self.is_conflict_free(set)
            && (0..self.arg_count).all(|a| set.contains(&a) || self.attacked_by_set(a, set))
    }
}

/// Insert `x` into the sorted vector `list`, keeping it sorted. Returns
/// `false`, leaving `list` unchanged, if `x` was already present.
fn insert_sorted(list: &mut Vec<usize>, x: usize) -> bool {
    match list.binary_search(&x) {
        Ok(_) => false,
        Err(pos) => {
            list.insert(pos, x);
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_af() {
        let mut af = AF::new(10);
        af.add_attack(1, 2);
        af.add_attack(1, 3);
        af.add_attack(1, 2);
        af.add_attack(3, 1);

        assert_eq!(af.argument_count(), 10);
        assert_eq!(af.attack_count(), 3);

        // assert_eq!(af.get_victims(1).collect()::<Vec<_>>, HashSet::from([2,3]));
        let mut res :HashSet<usize> = HashSet::new();
        for v in af.victims(1) {
            res.insert(*v);
        }
        assert_eq!(res, HashSet::from([2, 3]));

        let mut res :HashSet<usize> = HashSet::new();
        for a in af.attackers(2) {
            res.insert(*a);
        }
        assert_eq!(res, HashSet::from([1]));

        assert!(af.attacks(1, 2));
        assert!(!af.attacks(2, 2));

        assert!(af.attacks_set(1, &HashSet::from([3, 4])));
        assert!(!af.attacks_set(1, &HashSet::from([4, 5])));
        assert!(!af.attacks_set(2, &HashSet::from([1])))
    }

    fn build_chain_af() -> AF {
        // Chain 0 -> 1 -> 2 -> 3.
        let mut af = AF::new(4);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        af.add_attack(2, 3);
        af
    }

    #[test]
    fn test_is_conflict_free() {
        let af = build_chain_af();
        assert!(af.is_conflict_free(&HashSet::from([0, 2])));
        assert!(!af.is_conflict_free(&HashSet::from([0, 1])), "0 attacks 1");
    }

    #[test]
    fn test_is_complete_chain() {
        let af = build_chain_af();
        // The grounded extension {0, 2} is the (unique) complete extension.
        assert!(af.is_complete(&HashSet::from([0, 2])));
        assert!(!af.is_complete(&HashSet::new()), "0 is unattacked, so empty set is not complete");
        assert!(!af.is_complete(&HashSet::from([0])), "0 defends 2, so 2 must also be included");
        assert!(!af.is_complete(&HashSet::from([0, 1, 2])), "0 attacks 1: not conflict-free");
    }

    #[test]
    fn test_is_stable_chain() {
        let af = build_chain_af();
        // {0, 2} attacks 1 and 3 -- everything outside itself: stable.
        assert!(af.is_stable(&HashSet::from([0, 2])));
    }

    #[test]
    fn test_is_stable_odd_cycle_has_none() {
        // 0 -> 1 -> 2 -> 0: no stable extension exists.
        let mut af = AF::new(3);
        af.add_attack(0, 1);
        af.add_attack(1, 2);
        af.add_attack(2, 0);

        assert!(!af.is_stable(&HashSet::new()));
        assert!(!af.is_stable(&HashSet::from([0])));
        assert!(!af.is_stable(&HashSet::from([0, 1])));
    }

    #[test]
    fn test_is_complete_self_attack_prevents_defense() {
        // 0 self-attacks (so it can never be in any conflict-free set) and
        // 0 attacks 1. Defending 1 would require attacking 0, but nothing
        // except 0 itself ever attacks 0 -- so 1 can never be defended
        // either. The only complete extension is the empty set.
        let mut af = AF::new(2);
        af.add_attack(0, 0);
        af.add_attack(0, 1);

        assert!(af.is_complete(&HashSet::new()));
        assert!(!af.is_complete(&HashSet::from([0])), "0 self-attacks, not conflict-free");
        assert!(!af.is_complete(&HashSet::from([1])), "1 is never actually defended");
        assert!(!af.is_complete(&HashSet::from([0, 1])), "0 self-attacks, not conflict-free");
    }
}
