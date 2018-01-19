//! A type system which is Rank-2 fragment of System F.

enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

pub mod lambda2_restricted {
    enum Open {
        Var(usize, usize),
        Arr(Box<Open>, Box<Open>),
    }

    enum Restricted1 {
        Open(Open),
        Forall(Box<Restricted1>),
    }

    enum Restricted2 {
        Var(usize, usize),
        Arr(Restricted1, Box<Restricted2>),
        Forall(Box<Restricted2>),
    }

    pub mod lambda2 {
        enum Type {
            Var(usize, usize),
            Arr(Box<Type>, Box<Type>),
            Forall(Box<Type>),
        }
    }
}
