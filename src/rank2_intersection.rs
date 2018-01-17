//! A system of rank 2 intersection types.

use std::cmp::Ordering;

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Eq, Hash, PartialEq)]
enum Type<S, T> {
    Var(usize, usize),
    Arr(S, Box<T>),
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum SimpleType {
    Type(Type<Box<SimpleType>, SimpleType>),
}

#[derive(Clone, PartialEq)]
enum Rank1 {
    Type(SimpleType),
    Intersection(Box<Rank1>, Box<Rank1>),
}

#[derive(Clone, PartialEq)]
enum Rank2 {
    Type(Type<Rank1, Rank2>),
    Intersection(Box<Rank2>, Box<Rank2>),
}

struct Subst(HashMap<usize, SimpleType>);

enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

struct Env<T>(Vec<T>);

trait Types {
    fn ftv(&Self) -> HashSet<usize>;
}

impl Rank1 {
    fn simple_types(self) -> HashSet<SimpleType> {
        use self::Rank1::*;
        let mut types = HashSet::new();
        match self {
            Type(t) => {
                types.insert(t);
            }
            Intersection(t1, t2) => {
                types.extend(t1.simple_types());
                types.extend(t2.simple_types());
            }
        }
        types
    }
}

impl PartialOrd for Rank1 {
    fn partial_cmp(&self, t: &Rank1) -> Option<Ordering> {
        let t1: Rank1 = self.clone();
        let t2: Rank1 = t.clone();

        let s1 = t1.simple_types();
        let s2 = t2.simple_types();

        if s1 == s2 {
            Some(Ordering::Equal)
        } else if s1.is_subset(&s2) {
            Some(Ordering::Less)
        } else if s1.is_superset(&s2) {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! var {
        ($x:expr, $n:expr) => {
            Rank1::Type(SimpleType::Type(Type::Var($x, $n)))
        }
    }

    macro_rules! arr {
        ($t1:expr, $t2:expr) => {
            Rank1::Simple(SimpleType::Arr(Box::new($t1), Box::new($t2)))
        }
    }

    macro_rules! inter {
        ($t1:expr, $t2:expr) => {
            Rank1::Intersection(Box::new($t1), Box::new($t2))
        }
    }

    #[test]
    fn test_rank1_partial_order() {
        assert!(var!(0, 1) <= var!(0, 1));
        assert!(var!(0, 1) >= var!(0, 1));
        assert!(!(var!(0, 1) < var!(0, 1)));
        assert!(!(var!(0, 1) > var!(0, 1)));

        assert!(inter!(var!(0, 1), var!(0, 1)) <= inter!(var!(0, 1), var!(0, 1)));
        assert!(inter!(var!(0, 1), var!(0, 1)) >= inter!(var!(0, 1), var!(0, 1)));
        assert!(var!(0, 1) <= inter!(var!(0, 1), var!(0, 1)));
        assert!(var!(0, 1) >= inter!(var!(0, 1), var!(0, 1)));

        assert!(var!(0, 1) < inter!(var!(0, 1), var!(1, 2)));
    }
}
