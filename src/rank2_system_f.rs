//! A type system which is Rank-2 fragment of System F.

enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

impl Term {
    fn act(&self) -> Vec<usize> {
        use self::Term::*;
        match *self {
            Var(..) => Vec::new(),
            Abs(ref t) => {
                let mut v: Vec<usize> = t.act().iter_mut().map(|&mut n| n + 1).collect();
                v.push(0);
                v
            }
            App(ref t1, _) => {
                let mut v = t1.act();
                v.pop();
                v
            }
        }
    }
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

    #[derive(Clone, Copy)]
    enum Index {
        Companion,
        Left,
        Right,
    }

    #[derive(Clone)]
    enum Term {
        Var(usize, usize),
        Abs(Index, Box<Term>),
        App(Box<Term>, Box<Term>),
    }

    macro_rules! abs {
        ($t1:expr, $t2:expr) => {
            Abs($t1, Box::new($t2))
        }
    }
    macro_rules! app {
        ($t1:expr, $t2:expr) => {
            App(Box::new($t1), Box::new($t2))
        }
    }

    impl Term {
        /// Performs theta-reduction.
        fn reduce(mut self) -> Option<Self> {
            use self::Term::*;
            use self::Index::*;
            // TODO: need to prove correctness.
            match self {
                App(v1, v3) => {
                    let v1 = *v1;
                    match v1.clone() {
                        App(v2, v4) => {
                            let v2 = *v2;
                            if let Abs(Companion, v5) = v2 {
                                // theta 1
                                return Some(App(
                                    Box::new(abs!(Companion, App(v5, Box::new(v3.shift(1))))),
                                    v4,
                                ));
                            }
                        }
                        Abs(Companion, v8) => {
                            if let Abs(Left, v9) = *v8 {
                                // theta 4
                                return Some(abs!(
                                    Left,
                                    app!(abs!(Companion, v9.swap(0, 1)), v3.shift(1))
                                ));
                            }
                        }
                        _ => (),
                    }
                    let v3 = *v3;
                    if let App(v6, q) = v3 {
                        if let Abs(Companion, v7) = *v6 {
                            // theta 3
                            return Some(App(
                                Box::new(abs!(Companion, App(Box::new(v1.shift(1)), v7))),
                                q,
                            ));
                        }
                    }
                    None
                }
                Abs(Right, t) => {
                    let t = *t;
                    match t {
                        App(t, p) => {
                            let t = *t;
                            match t {
                                Abs(Companion, n) => {
                                    // theta 2
                                    let l = 0; // FIXME: the length of the context.
                                    let t1 = abs!(
                                        Companion,
                                        abs!(
                                            Right,
                                            n.shift_above(1, 1).subst_top(
                                                app!(Var(1, l), Var(0, l)),
                                            )
                                        )
                                    );
                                    let t2 = abs!(Right, p.subst_top(Var(0, l)));
                                    return Some(app!(t1, t2));
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }

        fn map<F>(self, onvar: &F, c: usize) -> Self
        where
            F: Fn(usize, usize, usize) -> Self,
        {
            use self::Term::*;
            match self {
                Var(x, n) => onvar(c, x, n),
                Abs(i, t) => abs!(i, t.map(onvar, c + 1)),
                App(t1, t2) => app!(t1.map(onvar, c), t2.map(onvar, c)),
            }
        }

        fn shift_above(self, c: usize, d: isize) -> Self {
            use self::Term::*;
            let var = |x, n| Var(x as usize, n as usize);
            let f = |c: usize, x: usize, n| if x >= c {
                var(x as isize + d, n as isize + d)
            } else {
                Var(x, (n as isize + d) as usize)
            };
            self.map(&f, c)
        }

        fn shift(self, d: isize) -> Self {
            self.shift_above(0, d)
        }

        fn subst(self, j: usize, t: Term) -> Self {
            use self::Term::*;
            let f = |j, x, n| if x == j {
                t.clone().shift(j as isize)
            } else {
                Var(x, n)
            };
            self.map(&f, j)
        }

        fn subst_top(self, t: Term) -> Self {
            self.subst(0, t)
        }

        /// Swaps the two indices.
        fn swap(self, i: usize, j: usize) -> Self {
            use self::Term::*;
            let f = |c, x, n| {
                let i = c + i;
                let j = c + j;
                if x == i {
                    Var(j, n)
                } else if x == j {
                    Var(i, n)
                } else {
                    Var(x, n)
                }
            };
            self.map(&f, 0)
        }
    }

    impl From<super::Term> for Term {
        fn from(t: super::Term) -> Self {
            let v = t.act();
            label(t, v, Index::Left, 0)
        }
    }

    fn label(t: super::Term, v: Vec<usize>, i: Index, x: usize) -> Term {
        use self::Term::*;
        match t {
            super::Term::Var(x, n) => Var(x, n),
            super::Term::Abs(t) => {
                let no_companion = v.contains(&x);
                let tt = Box::new(label(*t, v, i, x + 1));
                if no_companion {
                    Abs(i, tt)
                } else {
                    Abs(Index::Companion, tt)
                }
            }
            super::Term::App(t1, t2) => {
                let v1 = t2.act();
                App(
                    Box::new(label(*t1, v, i, x)),
                    Box::new(label(*t2, v1, Index::Right, x)),
                )
            }
        }
    }

    impl Restricted1 {
        fn shift_above(self, c: usize, d: isize) -> Self {
            use self::Restricted1::*;
            let Forall(n, t) = self;
            Forall(n, t.shift_above(c + n, d))
        }

        fn shift(self, d: isize) -> Self {
            self.shift_above(0, d)
        }
    }

    impl From<Rank1> for Restricted1 {
        fn from(t: Rank1) -> Self {
            use self::Restricted1::*;
            match t {
                RankN::Var(x, n) => Forall(0, Rank0::Var(x, n)),
                RankN::Arr(t1, t2) => {
                    match Self::from(*t2) {
                        Forall(n, t2) => Forall(n, Rank0::Arr(Box::new(t1.shift(n as isize)), Box::new(t2))),
                    }
                }
                RankN::Forall(t) => {
                    match Self::from(*t) {
                        Forall(n, t) => Forall(n + 1, t),
                    }
                }
                // TODO: Is this correct?
                RankN::Sharp(t) => Self::from(*t),
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
                    Forall(n, Restricted2::Arr(Restricted1::from(t1.shift(n as isize)), Box::new(t2)))
                }
                RankN::Forall(t) => {
                    let Forall(n, t) = Self::from(*t);
                    Forall(n + 1, t)
                }
                // TODO: Is this correct?
                RankN::Sharp(t) => Self::from(*t),
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
            Sharp(Box<RankN<T>>),
        }

        pub type Rank1 = RankN<Rank0>;
        pub type Rank2 = RankN<Rank1>;

        impl Rank0 {
            pub fn shift_above(self, c: usize, d: isize) -> Self {
                use self::Rank0::*;
                match self {
                    Var(x, n) => {
                        let n = n as isize;
                        if x >= c {
                            let x = x as isize;
                            Var((x + d) as usize, (n + d) as usize)
                        } else {
                            Var(x, (n + d) as usize)
                        }
                    }
                    Arr(t1, t2) => {
                        Arr(
                            Box::new(t1.shift_above(c, d)),
                            Box::new(t2.shift_above(c, d)),
                        )
                    }
                }
            }

            pub fn shift(self, d: isize) -> Self {
                self.shift_above(0, d)
            }
        }

        impl Rank1 {
            pub fn shift_above(self, c: usize, d: isize) -> Self {
                use self::RankN::*;
                match self {
                    Var(x, n) => {
                        let n = n as isize;
                        if x >= c {
                            let x = x as isize;
                            Var((x + d) as usize, (n + d) as usize)
                        } else {
                            Var(x, (n + d) as usize)
                        }
                    }
                    Arr(t1, t2) => {
                        Arr(
                            t1.shift_above(c, d),
                            Box::new(t2.shift_above(c, d)),
                        )
                    }
                    Forall(t) => {
                        Forall(Box::new(t.shift_above(c + 1, d)))
                    }
                    Sharp(t) => {
                        Sharp(Box::new(t.shift_above(c + 1, d)))
                    }
                }
            }

            pub fn shift(self, d: isize) -> Self {
                self.shift_above(0, d)
            }
        }
    }
}
