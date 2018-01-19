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
        fn from(t: Rank1) -> Restricted1 {
            match t {
                RankN::Var(x, n) => Restricted1::Forall(0, Rank0::Var(x, n)),
                RankN::Arr(t1, t2) => {
                    match Restricted1::from(*t2) {
                        Restricted1::Forall(n, t2) => {
                            Restricted1::Forall(n, Rank0::Arr(Box::new(t1), Box::new(t2)))
                        }
                    }
                }
                RankN::Forall(t) => {
                    match Restricted1::from(*t) {
                        Restricted1::Forall(n, t) => Restricted1::Forall(n + 1, t),
                    }
                }
            }
        }
    }

    impl From<Rank2> for Restricted2F {
        fn from(t: Rank2) -> Restricted2F {
            match t {
                RankN::Var(x, n) => Restricted2F::Forall(0, Restricted2::Var(x, n)),
                RankN::Arr(t1, t2) => {
                    let Restricted2F::Forall(n, t2) = Restricted2F::from(*t2);
                    Restricted2F::Forall(n, Restricted2::Arr(Restricted1::from(t1), Box::new(t2)))
                }
                RankN::Forall(t) => {
                    let Restricted2F::Forall(n, t) = Restricted2F::from(*t);
                    Restricted2F::Forall(n + 1, t)
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
