//! A system of rank 2 intersection types.

use std::collections::HashMap;

enum SimpleType {
    Var(usize, usize),
    Arr(Box<SimpleType>, Box<SimpleType>),
}

enum RankN<T> {
    Var(usize, usize),
    Arr(T, Box<RankN<T>>),
    Intersection(Box<RankN<T>>, Box<RankN<T>>),
}

type Rank1 = RankN<SimpleType>;

type Rank2 = RankN<Rank1>;

struct Subst(HashMap<usize, SimpleType>);

enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}
