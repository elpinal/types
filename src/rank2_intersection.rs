//! A system of rank 2 intersection types.

enum SimpleType {
    Var(usize, usize),
    Arr(Box<SimpleType>, Box<SimpleType>),
}

enum Rank1 {
    Var(usize, usize),
    Arr(SimpleType, Box<Rank1>),
    Intersection(Box<Rank1>, Box<Rank1>),
}

enum Rank2 {
    Var(usize, usize),
    Arr(Rank1, Box<Rank2>),
    Intersection(Box<Rank2>, Box<Rank2>),
}
