//! Another approach to rank 2 intersection types.

enum SimpleType {
    Var(String),
    Arr(Box<SimpleType>, Box<SimpleType>),
}

enum Rank1 {
    Simple(SimpleType),
    Intersection(Box<Rank1>, Box<Rank1>),
}

enum Rank2 {
    Simple(SimpleType),
    Arr(Rank1, Box<Rank2>),
}

enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

type Context = Vec<Rank1>;

struct Inference {
    n: usize,
}

impl Inference {
    fn fresh_var(&mut self) -> SimpleType {
        SimpleType::Var(format!("{}", self.n))
    }
}
