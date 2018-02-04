//! Label-selective lambda calculus.

pub mod symbolic {
    #[derive(Clone)]
    enum Term {
        Var(usize, usize),
        Abs(String, Box<Term>),
        App(String, Box<Term>, Box<Term>),
    }
}
