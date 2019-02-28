//! Label-selective lambda calculus.
//!
//! ## Reference
//!
//! Jacques Garrigue and Hassan Aït-Kaci. The typed polymorphic label-selective
//! lambda-calculus. ACM Symposium on Principles of Programming Languages (POPL), Portland,
//! Oregon, pages 35-47, 1994.

#[cfg(ignore)]
pub mod symbolic {
    use {Shift, ShiftRef, Subst, SubstRef};

    #[derive(Clone)]
    enum Term {
        Var(usize, usize),
        Abs(String, Box<Term>),
        App(String, Box<Term>, Box<Term>),
    }

    impl Term {
        fn eval(&mut self) -> bool {
            loop {
                if self.eval1() {
                    changed = true;
                } else {
                    return changed;
                }
            }
        }

        fn eval1(&mut self) -> bool {
            use self::Term::*;
            match *self {
                Var(..) => false,
                Abs(..) => false,
                App(ref l, ref t1, ref t2) => match *t1 {
                    Var(..) => t2.eval1(),
                    Abs(ref m, ref t) => {
                        if l == m {
                            t.subst_top(&t2);
                            return true;
                        }
                        t1.lift(l)
                    }
                    App(ref m, ref u1, ref u2) => {
                        if !t1.eval1() {
                            t2.eval1()
                        } else {
                            true
                        }
                    }
                },
            }
        }

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

        fn lift(&mut self, l: String) -> bool {
            use self::Term::*;
            match *self {
                Abs(ref m, ref t) => {
                    if m == l {
                        return false;
                    }
                    if t.lift() {
                        return true;
                    }
                    match *t {
                        Abs(ref n, ref t) => {
                            if n == l {
                                t.swap(0, 1);
                                *self = Abs(n, Abs(m, t));
                                return true;
                            }
                            return false;
                        }
                        _ => false,
                    }
                }
                _ => self.eval1(),
            }
        }

        fn swap(&mut self, i: usize, j: usize) {
            use self::Term::*;
            let f = |c: usize, x: usize, n, t: &mut Term| {
                if x == i + c {
                    *t = Var(j + c, n);
                } else if x == j + c {
                    *t = Var(i + c, n);
                }
            };
            self.map_ref(&f, 0);
        }
    }

    impl ShiftRef for Term {
        fn shift_above_ref(&mut self, c: usize, d: isize) {
            use self::Term::*;
            let var = |x, n| Var(x as usize, n as usize);
            let f = |c: usize, x: usize, n, t: &mut Term| {
                if x >= c {
                    *t = var(x as isize + d, n as isize + d);
                } else {
                    *t = Var(x, (n as isize + d) as usize);
                }
            };
            self.map_ref(&f, c);
        }
    }

    impl SubstRef for Term {
        fn subst_ref(&mut self, j: usize, t: &Self) {
            let f = |j, x, n, t0: &mut Self| {
                if x == j {
                    *t0 = t.clone().shift(j as isize);
                } else {
                    *t0 = Term::Var(x, n);
                }
            };
            self.map_ref(&f, j)
        }
    }
}
