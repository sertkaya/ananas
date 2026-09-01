use std::collections::hash_set::Iter;
use std::collections::HashSet;
use std::fmt::{Display, Formatter};

// Argumentation framework represented as adjacency list.
// Arguments are 32-bit unsigned integers.
pub struct AF {
    // Number of arguments
    arg_count: usize,
    // Adjacency list for attacks relation
    // Vector of hash sets.
    attacks: Vec<HashSet<usize>>,
    // Adjacency list for attacked-by relation
    // Vector of hash sets.
    attacked_by: Vec<HashSet<usize>>,
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
    // Create a new argumentation framework with the given number of arguments
    pub fn new(size: usize) -> AF {
        let attacks: Vec<HashSet<usize>> = vec![HashSet::new(); size];
        let attacked_by: Vec<HashSet<usize>> = vec![HashSet::new(); size];
        AF { arg_count: size, attacks, attacked_by }
    }

    // Add an attack from the attacker to the victim
    pub fn add_attack(&mut self, attacker: usize, victim: usize) {
        // add the attack to the attacks relation
        self.attacks[attacker].insert(victim);
        // add the attack to the attacked-by relation
        self.attacked_by[victim].insert(attacker);
    }

    // Get the unmber of arguments
    pub fn argument_count(&self) -> usize { self.arg_count }

    // Get the number of attacks
    pub fn attack_count(&self) ->usize  {
        self.attacks.iter().map(|s| s.len()).sum()
    }

    // Get the victims of an argument
    pub fn victims<'a>(&'a self, arg: usize) -> Iter<'a, usize> {
        self.attacks[arg].iter()
    }

    // Get the number of attackers of an argument
    pub fn attacker_count(&self, a: usize) -> usize {
        self.attacked_by[a].len()
    }

    // Get the attackers of an argument
    pub fn attackers<'a>(&'a self, arg: usize) -> Iter<'a, usize> {
        self.attacked_by[arg].iter()
    }

    // Check if argument a attacks argument b
    pub fn attacks(&self, a: usize, b: usize) -> bool {
        self.attacks[a].contains(&b)
    }

    // Check if argument a attacks any argument in the set s
    pub fn attacks_set(&self, a: usize, s: &HashSet<usize>) -> bool {
        !self.attacks[a].is_disjoint(s)
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

        assert_eq!(af.attacks(1, 2), true);
        assert_eq!(af.attacks(2, 2), false);

        assert_eq!(af.attacks_set(1, &HashSet::from([3, 4])), true);
        assert_eq!(af.attacks_set(1, &HashSet::from([4, 5])), false);
        assert_eq!(af.attacks_set(2, &HashSet::from([1])), false)
    }
}
