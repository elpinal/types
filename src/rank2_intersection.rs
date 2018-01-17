//! A system of rank 2 intersection types.

use std::collections::HashMap;
use std::collections::HashSet;

enum SimpleType {
    Var(usize, usize),
    Arr(Box<SimpleType>, Box<SimpleType>),
}

enum Rank1 {
    Var(usize, usize),
    Arr(SimpleType, SimpleType),
    Intersection(Box<Rank1>, Box<Rank1>),
}

enum Rank2 {
    Var(usize, usize),
    Arr(Rank1, Box<Rank2>),
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
