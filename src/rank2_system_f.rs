//! A type system which is Rank-2 fragment of System F.

enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

pub mod lambda2_restricted {
    use self::lambda2::*;

    enum Restricted1 {
        Forall(usize, Rank0),
    }

    enum Restricted2 {
        Var(usize, usize),
        Arr(Restricted1, Box<Restricted2>),
    }

    enum Restricted2F {
        Forall(usize, Restricted2),
    }

    impl From<Rank1> for Restricted1 {
        fn from(t: Rank1) -> Self {
            use self::Restricted1::*;
            match t {
                RankN::Var(x, n) => Forall(0, Rank0::Var(x, n)),
                RankN::Arr(t1, t2) => {
                    match Self::from(*t2) {
                        Forall(n, t2) => Forall(n, Rank0::Arr(Box::new(t1), Box::new(t2))),
                    }
                }
                RankN::Forall(t) => {
                    match Self::from(*t) {
                        Forall(n, t) => Forall(n + 1, t),
                    }
                }
            }
        }
    }

    impl From<Rank2> for Restricted2F {
        fn from(t: Rank2) -> Self {
            use self::Restricted2F::*;
            match t {
                RankN::Var(x, n) => Forall(0, Restricted2::Var(x, n)),
                RankN::Arr(t1, t2) => {
                    let Forall(n, t2) = Self::from(*t2);
                    Forall(n, Restricted2::Arr(Restricted1::from(t1), Box::new(t2)))
                }
                RankN::Forall(t) => {
                    let Forall(n, t) = Self::from(*t);
                    Forall(n + 1, t)
                }
            }
        }
    }

    pub mod lambda2 {
        pub enum Rank0 {
            Var(usize, usize),
            Arr(Box<Rank0>, Box<Rank0>),
        }

        pub enum RankN<T> {
            Var(usize, usize),
            Arr(T, Box<RankN<T>>),
            Forall(Box<RankN<T>>),
        }

        pub type Rank1 = RankN<Rank0>;
        pub type Rank2 = RankN<Rank1>;
    }
}
