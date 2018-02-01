/// A linear type system.

use std::cmp::Ordering;
use std::iter::Iterator;

#[derive(Clone, Copy, PartialEq)]
enum Qual {
    Linear,
    Unrestricted,
}

enum Term {
    Var(usize, usize),
    Bool(Qual, Bool),
    If(Box<Term>, Box<Term>, Box<Term>),
    Pair(Qual, Box<Term>, Box<Term>),
    Split(Box<Term>, Box<Term>),
    Abs(Qual, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

enum Bool {
    True,
    False,
}

struct Type(Qual, Box<Pretype>);

enum Pretype {
    Bool,
    Pair(Type, Type),
    Arr(Type, Type),
}

struct Context(Vec<Type>);

impl PartialOrd for Qual {
    fn partial_cmp(&self, q: &Self) -> Option<Ordering> {
        use self::Qual::*;
        use self::Ordering::*;
        if *self == Unrestricted && *q == Linear {
            return Some(Greater);
        }
        if *self == Linear && *q == Unrestricted {
            return Some(Less);
        }
        if self == q { Some(Equal) } else { None }
    }
}

trait Containment {
    fn can_appear_in(&self, q: Qual) -> bool;
}

impl Containment for Type {
    fn can_appear_in(&self, q1: Qual) -> bool {
        let Type(q2, _) = *self;
        q1 <= q2
    }
}

impl Iterator for Context {
    type Item = Type;
    /// Returns a type which the most recently bound variable has.
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_partial_ord_for_qual() {
        use self::Qual::*;

        assert!(Unrestricted <= Unrestricted);
        assert!(Linear <= Unrestricted);
        assert!(Linear <= Linear);

        assert!(Unrestricted >= Unrestricted);
        assert!(!(Linear >= Unrestricted));
        assert!(Linear >= Linear);

        assert!(!(Unrestricted <= Linear));
    }
}
