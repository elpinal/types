//! System F
#![warn(missing_docs)]

/// Represents a type.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// A type variable. As given `Var(x, n)`, `x` represents de Bruijn index; `n` represents the
    /// size of the context.
    Var(isize, isize),
    /// An arrow type.
    Arr(Box<Type>, Box<Type>),
    /// An universal type. `String` is for the name of the binding type variable.
    All(String, Box<Type>),
    /// An existential type. `String` is for the name of the binding type variable.
    Some(String, Box<Type>),
}

impl Type {
    fn map<F>(self, onvar: &F, c: isize) -> Type
    where
        F: Fn(isize, isize, isize) -> Type,
    {
        match self {
            Type::Var(x, n) => onvar(c, x, n),
            Type::Arr(ty1, ty2) => {
                Type::Arr(Box::new(ty1.map(onvar, c)), Box::new(ty2.map(onvar, c)))
            }
            Type::All(i, ty) => Type::All(i, Box::new(ty.map(onvar, c))),
            Type::Some(i, ty) => Type::Some(i, Box::new(ty.map(onvar, c))),
        }
    }

    fn shift_above(self, d: isize, c: isize) -> Type {
        let f = |c, x, n| if x >= c {
            Type::Var(x + d, n + d)
        } else {
            Type::Var(x, n + d)
        };
        self.map(&f, c)
    }

    fn shift(self, d: isize) -> Type {
        self.shift_above(d, 0)
    }

    fn subst(self, ty: &Type, j: isize) -> Type {
        let f = |j, x, n| if x == j {
            ty.clone().shift(j)
        } else {
            Type::Var(x, n)
        };
        self.map(&f, j)
    }

    fn subst_top(self, ty: Type) -> Type {
        self.subst(&ty.shift(1), 0).shift(-1)
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Term {
    Var(isize, isize),
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
    TAbs(String, Box<Term>),
    TApp(Box<Term>, Type),
    Pack(Type, Box<Term>, Type),
    Unpack(String, String, Box<Term>, Box<Term>),
}

impl Term {
    fn map<F, G>(self, onvar: &F, ontype: &G, c: isize) -> Term
    where
        F: Fn(isize, isize, isize) -> Term,
        G: Fn(isize, Type) -> Type,
    {
        match self {
            Term::Var(x, n) => onvar(c, x, n),
            Term::Abs(x, ty, t) => {
                Term::Abs(x, ontype(c, ty), Box::new(t.map(onvar, ontype, c + 1)))
            }
            Term::App(t1, t2) => {
                Term::App(
                    Box::new(t1.map(onvar, ontype, c)),
                    Box::new(t2.map(onvar, ontype, c)),
                )
            }
            Term::TAbs(i, t) => Term::TAbs(i, Box::new(t.map(onvar, ontype, c + 1))),
            Term::TApp(t, ty) => Term::TApp(Box::new(t.map(onvar, ontype, c)), ontype(c, ty)),
            Term::Pack(ty1, t, ty2) => {
                Term::Pack(
                    ontype(c, ty1),
                    Box::new(t.map(onvar, ontype, c)),
                    ontype(c, ty2),
                )
            }
            Term::Unpack(tyi, ti, t1, t2) => {
                Term::Unpack(
                    tyi,
                    ti,
                    Box::new(t1.map(onvar, ontype, c)),
                    Box::new(t2.map(onvar, ontype, c + 2)),
                )
            }
        }
    }

    fn shift_above(self, d: isize, c: isize) -> Term {
        let f = |c, x, n| if x >= c {
            Term::Var(x + d, n + d)
        } else {
            Term::Var(x, n + d)
        };
        let g = |c, ty: Type| ty.shift_above(d, c);
        self.map(&f, &g, c)
    }

    fn shift(self, d: isize) -> Term {
        self.shift_above(d, 0)
    }

    fn subst(self, t: &Term, j: isize) -> Term {
        let f = |j, x, n| if x == j {
            t.clone().shift(j)
        } else {
            Term::Var(x, n)
        };
        let g = |_, t| t;
        self.map(&f, &g, j)
    }

    fn subst_top(self, t: Term) -> Term {
        self.subst(&t.shift(1), 0).shift(-1)
    }

    fn subst_type(self, ty1: Type, j: isize) -> Term {
        let f = |_, x, n| Term::Var(x, n);
        let g = |j, ty2: Type| ty2.subst(&ty1, j);
        self.map(&f, &g, j)
    }

    fn subst_type_top(self, ty: Type) -> Term {
        self.subst_type(ty.shift(1), 0).shift(-1)
    }
}

enum Eval {
    Next(Term),
    Stuck(Term),
}

fn eval1(tm: Term) -> Eval {
    match tm {
        Term::App(t1, t2) => {
            match eval1(*t1) {
                Eval::Next(t11) => Eval::Next(Term::App(Box::new(t11), t2)),
                Eval::Stuck(t1) => {
                    match eval1(*t2) {
                        Eval::Next(t21) => Eval::Next(Term::App(Box::new(t1), Box::new(t21))),
                        Eval::Stuck(t2) => {
                            match t1 {
                                Term::Abs(_, _, t) => Eval::Next(t.subst_top(t2)),
                                _ => Eval::Stuck(Term::App(Box::new(t1), Box::new(t2))),
                            }
                        }
                    }
                }
            }
        }
        Term::TApp(t, ty) => {
            match eval1(*t) {
                Eval::Next(t1) => Eval::Next(Term::TApp(Box::new(t1), ty)),
                Eval::Stuck(t) => {
                    match t {
                        Term::TAbs(_, t2) => Eval::Next(t2.subst_type_top(ty)),
                        _ => Eval::Stuck(Term::TApp(Box::new(t), ty)),
                    }
                }
            }
        }
        _ => Eval::Stuck(tm),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! subst_test {
        ( $t1:expr, $t2:expr, $t3:expr ) => {
            assert_eq!($t2.clone().subst_top($t1.clone()), $t3.clone());
        };
    }

    macro_rules! all {
        ( $t1:expr, $t2:expr ) => {
            Type::All($t1.to_string(), Box::new($t2))
        };
    }

    #[test]
    fn test_subst_top() {
        use self::Type::*;

        let t = Var(0, 1);
        subst_test!(t, t, t);
        subst_test!(t, Var(0, 2), t);
        subst_test!(t, Var(1, 2), t);
        subst_test!(t, all!("X", Var(0, 3)), all!("X", Var(0, 1)));
    }
}
