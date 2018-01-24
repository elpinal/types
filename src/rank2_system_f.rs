//! A type system which is Rank-2 fragment of System F.

use {Shift, Subst};

#[derive(Clone)]
enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

macro_rules! abs {
    ($t1:expr) => {
        Term::Abs(Box::new($t1))
    }
}

macro_rules! app {
    ($t1:expr, $t2:expr) => {
        Term::App(Box::new($t1), Box::new($t2))
    }
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

    fn map<F>(self, onvar: &F, c: usize) -> Self
    where
        F: Fn(usize, usize, usize) -> Self,
    {
        use self::Term::*;
        match self {
            Var(x, n) => onvar(c, x, n),
            Abs(t) => abs!(t.map(onvar, c + 1)),
            App(t1, t2) => app!(t1.map(onvar, c), t2.map(onvar, c)),
        }
    }

    /// Swaps the two indices.
    pub fn swap(self, i: usize, j: usize) -> Self {
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

    fn rotate(self, n: usize) -> Self {
        self.shift(1).subst(n, &Term::Var(0, n))
    }
}

impl Shift for Term {
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
}

impl Subst for Term {
    fn subst(self, j: usize, t: &Self) -> Self {
        let f = |j, x, n| if x == j {
            t.clone().shift(j as isize)
        } else {
            Term::Var(x, n)
        };
        self.map(&f, j)
    }
}

struct Theta(usize, Vec<Term>);

impl From<Term> for Theta {
    fn from(t: Term) -> Theta {
        Theta::from_term(t, 0)
    }
}

impl Theta {
    fn from_right(t: Term, l: usize) -> Vec<Term> {
        use self::Term::*;
        match t {
            Var(..) => vec![t],
            Abs(t) => {
                let mut v = Theta::from_right(*t, l + 1);
                let mut i = v.len() + 1;
                v.into_iter()
                    .map(|t| {
                        i -= 1;
                        t.rotate(i)
                    })
                    .collect()
            }
            App(t, t1) => {
                let mut v1 = Theta::from_right(*t, l);
                let mut v2 = Theta::from_right(*t1, l);
                Theta::app_right(v1, v2)
            }
        }
    }

    fn app_right(v1: Vec<Term>, v2: Vec<Term>) -> Vec<Term> {
        let mut v1 = v1.into_iter();
        let mut v2 = v2.into_iter();
        v1.by_ref().map(
            |t| t.shift_above(1, (v2.len() - 1) as isize),
        );
        if let Some(t2) = v2.next() {
            let t2 = t2.shift_above(1, (v1.len() - 1) as isize);
            if let Some(t1) = v1.next() {
                let mut v1: Vec<_> = vec![app!(t1, t2)].into_iter().chain(v1).collect();
                v1.extend(v2);
                v1
            } else {
                panic!("empty term");
            }
        } else {
            panic!("empty term");
        }
    }

    fn from_term(t: Term, l: usize) -> Theta {
        use self::Term::*;
        match t {
            Var(..) => Theta(0, vec![t]),
            Abs(t) => {
                let Theta(n, v) = Theta::from_term(*t, l + 1);
                Theta(n + 1, v)
            }
            App(t, t1) => {
                let Theta(n, v) = Theta::from_term(*t, l);
                let v1 = Theta::app_right(v, Theta::from_right(*t1, l));
                Theta(n, v1)
            }
        }
    }
}

/// Acyclic Semi-Unification Problem.
pub mod asup {
    #![cfg(ignore)]
    use rank2_system_f::lambda2_restricted::lambda2::Rank0;
    use rank2_system_f::lambda2_restricted::Term;

    struct Instance(Vec<(Rank0, Rank0)>);

    struct Constructor {
        n: usize,
    }

    fn first_order(t1: Rank0, t2: Rank0) -> (Rank0, Rank0) {
        self.fresh
    }

    impl Constructor {
        fn fresh(&mut self) -> Rank0 {
            let n = self.n;
            self.n = self.n + 1;
            Var(n, n)
        }

        fn construct(t: Term) -> Instance {
            use self::Term::*;
            match t {
                Var() => (),
                Abs() => (),
                App() => (),
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
    pub enum Index {
        Companion,
        Left,
        Right,
    }

    #[derive(Clone)]
    pub enum Term {
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

    impl Shift for Term {
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
    }

    impl Term {
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

        fn subst(self, j: usize, t: Term) -> Self {
            use self::Term::*;
            let f = |j, x, n| if x == j {
                t.clone().shift(j as isize)
            } else {
                Var(x, n)
            };
            self.map(&f, j)
        }

        pub fn subst_top(self, t: Term) -> Self {
            self.subst(0, t)
        }

        /// Swaps the two indices.
        pub fn swap(self, i: usize, j: usize) -> Self {
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

    impl Shift for Restricted1 {
        fn shift_above(self, c: usize, d: isize) -> Self {
            use self::Restricted1::*;
            let Forall(n, t) = self;
            Forall(n, t.shift_above(c + n, d))
        }
    }

    impl From<Rank1> for Restricted1 {
        fn from(t: Rank1) -> Self {
            use self::Restricted1::*;
            match t {
                RankN::Var(x, n) => Forall(0, Rank0::Var(x, n)),
                RankN::Arr(t1, t2) => {
                    match Self::from(*t2) {
                        Forall(n, t2) => {
                            Forall(n, Rank0::Arr(Box::new(t1.shift(n as isize)), Box::new(t2)))
                        }
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
                    Forall(
                        n,
                        Restricted2::Arr(Restricted1::from(t1.shift(n as isize)), Box::new(t2)),
                    )
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
        pub use Shift;

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

        impl Shift for Rank0 {
            fn shift_above(self, c: usize, d: isize) -> Self {
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
        }

        impl Shift for Rank1 {
            fn shift_above(self, c: usize, d: isize) -> Self {
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
                    Arr(t1, t2) => Arr(t1.shift_above(c, d), Box::new(t2.shift_above(c, d))),
                    Forall(t) => Forall(Box::new(t.shift_above(c + 1, d))),
                    Sharp(t) => Sharp(Box::new(t.shift_above(c + 1, d))),
                }
            }
        }
    }
}
