//! Label-selective lambda calculus.

pub mod symbolic {
    use {Shift, ShiftRef, Subst, SubstRef};

    #[derive(Clone)]
    enum Term {
        Var(usize, usize),
        Abs(String, Box<Term>),
        App(String, Box<Term>, Box<Term>),
    }

    impl Term {
        fn map_ref<F>(&mut self, onvar: &F, c: usize)
        where
            F: Fn(usize, usize, usize, &mut Self),
        {
            use self::Term::*;
            match self {
                &mut Var(x, n) => onvar(c, x, n, self),
                &mut Abs(_, ref mut t) => {
                    t.map_ref(onvar, c + 1);
                }
                &mut App(_, ref mut t1, ref mut t2) => {
                    t1.map_ref(onvar, c);
                    t2.map_ref(onvar, c);
                }
            }
        }
    }

    impl ShiftRef for Term {
        fn shift_above_ref(&mut self, c: usize, d: isize) {
            use self::Term::*;
            let var = |x, n| Var(x as usize, n as usize);
            let f = |c: usize, x: usize, n, t: &mut Term| if x >= c {
                *t = var(x as isize + d, n as isize + d);
            } else {
                *t = Var(x, (n as isize + d) as usize);
            };
            self.map_ref(&f, c);
        }
    }

    impl SubstRef for Term {
        fn subst_ref(&mut self, j: usize, t: &Self) {
            let f = |j, x, n, t0: &mut Self| if x == j {
                *t0 = t.clone().shift(j as isize);
            } else {
                *t0 = Term::Var(x, n);
            };
            self.map_ref(&f, j)
        }
    }
}
