/// A linear type system.

use std::cmp::Ordering;

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

impl PartialOrd for Qual {
    fn partial_cmp(&self, q: &Self) -> Option<Ordering> {
        use self::Qual::*;
        if *self == Unrestricted && *q == Linear {
            return Some(Ordering::Greater);
        }
        if *self == Linear && *q == Unrestricted {
            return Some(Ordering::Less);
        }
        None
    }
}

trait Qualified {
    fn can_appear_in(&self, q: Qual) -> bool;
}

impl Qualified for Type {
    fn can_appear_in(&self, q1: Qual) -> bool {
        let Type(q2, _) = *self;
        q1 <= q2
    }
}
