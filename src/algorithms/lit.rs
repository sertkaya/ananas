//! The vocabulary of the search: values, literals, and the reasons and
//! outcomes of assigning them.

/// Whether an argument belongs to a node's set: decided either way, or not
/// yet decided
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    Undecided,
    In,
    Out,
}

/// Why an argument was assigned its value. Recorded with every assignment
/// so that a conflict can be traced back to the assignments that caused it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    /// In by assumption: the query argument, an unattacked argument, or a
    /// search decision
    Decision,
    /// Out because it attacks itself
    SelfAttack,
    /// Out because a search candidate's whole subtree failed with it in.
    /// Like a decision, it has no antecedents on the trail.
    RuledOut,
    /// Out because it attacks, or is attacked by, the given member
    Member(usize),
    /// In because every one of its attackers is known defeated
    Completeness,
    /// In because it is the only usable defender left against the given
    /// argument, which must be defeated: every other attacker of it is out
    OnlyDefender(usize),
    /// Forced by the learned clause with the given index: every other
    /// literal of it is false
    Clause(usize),
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

impl Lit {
    /// The opposite of an `In` or `Out` literal. `Def` has no opposite:
    /// nothing ever records that an argument must stay undefeated.
    pub fn negated(self) -> Lit {
        match self {
            Lit::In(a) => Lit::Out(a),
            Lit::Out(a) => Lit::In(a),
            Lit::Def(_) => panic!("Def literals have no negation"),
        }
    }
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
