//! A system of rank 2 intersection types.

use std::cmp::Ordering;

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Eq, Hash, PartialEq)]
enum SimpleType {
    Var(String),
    Arr(Box<SimpleType>, Box<SimpleType>),
}

#[derive(Clone, PartialEq)]
enum Rank1 {
    Simple(SimpleType),
    Intersection(Box<Rank1>, Box<Rank1>),
}

#[derive(Clone, PartialEq)]
enum Rank2 {
    Simple(SimpleType),
    Arr(Rank1, Box<Rank2>),
}

struct Subst(HashMap<String, SimpleType>);

enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

type Env<T> = HashMap<String, T>;

trait Types {
    fn ftv(&Self) -> HashSet<String>;
}

impl PartialOrd for Rank1 {
    fn partial_cmp(&self, t: &Rank1) -> Option<Ordering> {
        use std::cmp::Ordering::*;
        let s1 = self.simple_types();
        let s2 = t.simple_types();
        if s1 == s2 {
            Some(Equal)
        } else if s1.is_subset(&s2) {
            Some(Less)
        } else if s2.is_superset(&s1) {
            Some(Greater)
        } else {
            None
        }
    }
}

impl Rank1 {
    fn simple_types(&self) -> HashSet<SimpleType> {
        use self::Rank1::*;
        let mut types = HashSet::new();
        match *self {
            Simple(ref s) => {
                types.insert(s.clone());
            }
            Intersection(ref t1, ref t2) => {
                types.extend(t1.simple_types());
                types.extend(t2.simple_types());
            }
        }
        types
    }
}

impl PartialOrd for Rank2 {
    fn partial_cmp(&self, t: &Rank2) -> Option<Ordering> {
        use std::cmp::Ordering::*;
        use self::Rank2::*;
        match *self {
            Simple(..) if self == t => Some(Equal),
            Simple(..) => None,
            Arr(ref t1, ref t2) => {
                match *t {
                    Simple(SimpleType::Var(..)) => None,
                    Simple(SimpleType::Arr(ref s1, ref s2)) => {
                        let o1 = Rank1::Simple(*s1.clone()).partial_cmp(t1);
                        let o2 = t2.partial_cmp(&Box::new(Rank2::Simple(*s2.clone())));
                        if o1 == o2 { o1 } else { None }
                    }
                    Arr(ref s1, ref s2) => {
                        let o1 = s1.partial_cmp(t1);
                        let o2 = t2.partial_cmp(s2);
                        if o1 == o2 { o1 } else { None }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {}
}
