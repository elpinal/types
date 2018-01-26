//! A system of rank 2 intersection types.

use std::cmp::Ordering;

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Eq, Hash, PartialEq)]
enum SimpleType {
    Var(String),
    Arr(Box<SimpleType>, Box<SimpleType>),
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum Rank1 {
    Simple(SimpleType),
    Intersection(Box<Rank1>, Box<Rank1>),
}

#[derive(Clone, Eq, Hash, PartialEq)]
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

#[derive(Clone, PartialEq)]
struct Env<T>(HashMap<String, T>);

trait Types {
    fn ftv(&Self) -> HashSet<String>;
}

#[derive(Clone, PartialEq)]
struct Pair(Env<Rank1>, Rank2);

#[derive(Clone, Eq, Hash, PartialEq)]
enum Relation {
    Eq(SimpleType, SimpleType),
    Ne(Rank2, Rank1),
}

#[derive(Clone, PartialEq)]
struct Satisfaction(Vec<String>, HashSet<Relation>);

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

impl Rank2 {
    fn relation2_1(&self, t: &Rank1) -> Option<Ordering> {
        use std::cmp::Ordering::*;
        for s in t.simple_types().into_iter() {
            match self.partial_cmp(&Rank2::Simple(s)) {
                Some(Less) => (),
                _ => return None,
            }
        }
        Some(Less)
    }
}

impl PartialOrd for Env<Rank1> {
    fn partial_cmp(&self, e: &Env<Rank1>) -> Option<Ordering> {
        use std::cmp::Ordering::*;
        for (x, t2) in e.0.iter() {
            match self.0.get(x) {
                Some(t1) => {
                    if !(t1 <= &t2) {
                        return None;
                    }
                }
                _ => return None,
            }
        }
        Some(Less)
    }
}

impl PartialOrd for Pair {
    fn partial_cmp(&self, p: &Pair) -> Option<Ordering> {
        let o1 = p.0.partial_cmp(&self.0);
        let o2 = self.1.partial_cmp(&p.1);
        if o1 == o2 { o1 } else { None }
    }
}

impl Relation {
    fn to_equality(self) -> HashSet<Relation> {
        use self::Relation::*;
        macro_rules! set {
            ( $($e:expr),* ) => {
                {
                    let mut ss = HashSet::new();
                    $(
                        ss.insert($e);
                    )*
                    ss
                }
            }
        }
        macro_rules! arr {
            ($t11:expr, $t12:expr, $t2:expr, $s:expr) => {
                match $t2 {
                    Rank1::Simple(SimpleType::Var(..)) => unimplemented!(),
                    Rank1::Simple(SimpleType::Arr(t21, t22)) => {
                        set!(
                            Ne(Rank2::Simple(*t21), $t11),
                            Ne($t12, Rank1::Simple(*t22))
                        )
                    }
                    Rank1::Intersection(t21, t22) => {
                        set!(
                            Ne($s.clone(), *t21),
                            Ne($s, *t22)
                        )
                    }
                }
            }
        }
        match self {
            Eq(..) => set!(self),
            Ne(t1, t2) => {
                match t1 {
                    Rank2::Simple(s) => {
                        match s {
                            SimpleType::Var(..) => {
                                match t2 {
                                    Rank1::Simple(st) => set!(Eq(s, st)),
                                    Rank1::Intersection(t21, t22) => {
                                        set!(
                                            Ne(Rank2::Simple(s.clone()), *t21),
                                            Ne(Rank2::Simple(s), *t22)
                                        )
                                    }
                                }
                            }
                            SimpleType::Arr(t11, t12) => {
                                arr!(
                                    Rank1::Simple(*t11),
                                    Rank2::Simple(*t12),
                                    t2,
                                    Rank2::Simple(SimpleType::Arr(t11.clone(), t12.clone()))
                                )
                            }
                        }
                    }
                    Rank2::Arr(t11, t12) => {
                        arr!(t11, *t12, t2, Rank2::Arr(t11.clone(), t12.clone()))
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
