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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
    }
}
