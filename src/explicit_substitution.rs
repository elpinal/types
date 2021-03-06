//! Explicit substitution.

use std::rc::Rc;

/// A type.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// A type variable with the index.
    Var(usize),
    /// An universally-quantified type.
    Forall(Box<Type>),
    /// An arrow type.
    Arr(Box<Type>, Box<Type>),
    /// A closure.
    Closure(Box<Type>, Subst),
}

/// A substitution.
#[derive(Clone, Debug, PartialEq)]
pub enum Subst {
    Id,
    Shift,
    Cons(Rc<Type>, Box<Subst>),
    Comp(Box<Subst>, Box<Subst>),
}

impl Type {
    fn forall(t: Type) -> Type {
        Type::Forall(Box::new(t))
    }

    fn arr(t1: Type, t2: Type) -> Type {
        Type::Arr(Box::new(t1), Box::new(t2))
    }

    fn closure(t: Type, s: Subst) -> Type {
        Type::Closure(Box::new(t), s)
    }

    /// Reduces to the normal form.
    /// All conses must have the form `Subst::Cons(Type::Closure(..), _)`.
    fn nf(self, s0: Subst) -> Type {
        use self::Subst::*;
        use self::Type::*;
        let (t, s1) = self.whnf(s0);
        match t {
            Var(_) => t,
            Forall(t0) => Type::forall(t0.nf(Subst::cons(
                Type::closure(Var(0), Id),
                Subst::comp(s1, Shift),
            ))),
            Arr(t1, t2) => Type::arr(t1.nf(s1.clone()), t2.nf(s1)),
            Closure(..) => panic!("weak head normal forms do not include closures"),
        }
    }

    /// Reduces to the weak head normal form.
    fn whnf(self, s0: Subst) -> (Type, Subst) {
        use self::Subst::*;
        use self::Type::*;
        match self {
            Var(n) => match s0 {
                Id => (Var(n), Id),
                Shift => (Var(n + 1), Id),
                Cons(t, s) => {
                    if n == 0 {
                        match (*t).clone() {
                            Closure(t, s) => t.whnf(s),
                            _ => panic!("unexpected error"),
                        }
                    } else {
                        Var(n - 1).whnf(*s)
                    }
                }
                Comp(s1, s2) => Type::closure(self, *s1).whnf(*s2),
            },
            Closure(t, s) => match *t {
                Var(n) => match s {
                    Id => Var(n).whnf(s0),
                    Shift => Var(n + 1).whnf(s0),
                    Cons(t1, s1) => {
                        if n == 0 {
                            (*t1).clone().whnf(s0)
                        } else {
                            Type::closure(Var(n - 1), *s1).whnf(s0)
                        }
                    }
                    Comp(s1, s2) => Closure(t, *s1).whnf(Comp(s2, Box::new(s0))),
                },
                _ => t.whnf(Subst::comp(s, s0)),
            },
            _ => (self, s0),
        }
    }
}

impl Subst {
    fn cons(t: Type, s: Subst) -> Subst {
        Subst::Cons(Rc::new(t), Box::new(s))
    }

    fn comp(s1: Subst, s2: Subst) -> Subst {
        Subst::Comp(Box::new(s1), Box::new(s2))
    }
}

/// A context.
#[derive(Clone, Debug, PartialEq)]
pub struct Context(Vec<(Binding)>);

/// A binding.
#[derive(Clone, Debug, PartialEq)]
pub enum Binding {
    /// Denotes that a term have a type.
    Term(Type),
    /// Denotes a type.
    Type,
}

/// A term.
#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(usize),
    Abs(Type, Box<Term>),
    App(Box<Term>, Box<Term>),
    TAbs(Box<Term>),
    TApp(Box<Term>, Type),
}

#[cfg(test)]
mod tests {
    extern crate test;

    use super::*;
    use test::Bencher;

    #[test]
    fn test_nf() {
        use self::Subst::*;
        use self::Type::*;

        assert_eq!(Var(0).nf(Id), Var(0));
        assert_eq!(Var(20).nf(Id), Var(20));

        assert_eq!(Var(0).nf(Shift), Var(1));
        assert_eq!(Var(1).nf(Shift), Var(2));

        assert_eq!(
            Var(0).nf(Subst::cons(Type::closure(Var(0), Id), Shift)),
            Var(0)
        );
        assert_eq!(
            Var(0).nf(Subst::cons(Type::closure(Var(1), Id), Shift)),
            Var(1)
        );
        assert_eq!(
            Var(0).nf(Subst::cons(Type::closure(Var(21), Id), Shift)),
            Var(21)
        );

        assert_eq!(
            Var(1).nf(Subst::cons(Type::closure(Var(21), Id), Shift)),
            Var(1)
        );
        assert_eq!(
            Var(1).nf(Subst::cons(Type::closure(Var(21), Id), Id)),
            Var(0)
        );

        assert_eq!(Var(0).nf(Subst::comp(Id, Id)), Var(0));
        assert_eq!(Var(0).nf(Subst::comp(Id, Shift)), Var(1));
        assert_eq!(Var(0).nf(Subst::comp(Shift, Id)), Var(1));
        assert_eq!(Var(0).nf(Subst::comp(Shift, Shift)), Var(2));

        assert_eq!(Type::arr(Var(0), Var(0)).nf(Id), Type::arr(Var(0), Var(0)));
        assert_eq!(
            Type::arr(Var(0), Var(0)).nf(Shift),
            Type::arr(Var(1), Var(1))
        );

        assert_eq!(Type::forall(Var(0)).nf(Id), Type::forall(Var(0)));
        assert_eq!(Type::forall(Var(0)).nf(Shift), Type::forall(Var(0)));
        assert_eq!(Type::forall(Var(1)).nf(Shift), Type::forall(Var(2)));

        assert_eq!(
            Type::forall(Var(0)).nf(Subst::cons(Type::closure(Var(77), Id), Id)),
            Type::forall(Var(0))
        );
        assert_eq!(
            Type::forall(Var(1)).nf(Subst::cons(Type::closure(Var(77), Id), Id)),
            Type::forall(Var(78))
        );

        assert_eq!(
            Type::forall(Type::forall(Var(2))).nf(Subst::cons(Type::closure(Var(0), Id), Shift)),
            Type::forall(Type::forall(Var(2)))
        );

        assert_eq!(
            Type::forall(Type::forall(Var(2))).nf(Subst::cons(Type::closure(Var(0), Id), Id)),
            Type::forall(Type::forall(Var(2)))
        );
    }

    #[test]
    fn test_whnf() {
        use self::Subst::*;
        use self::Type::*;

        assert_eq!(
            Type::forall(Type::forall(Var(2))).whnf(Subst::cons(Type::closure(Var(0), Id), Shift)),
            (
                Type::forall(Type::forall(Var(2))),
                Subst::cons(Type::closure(Var(0), Id), Shift)
            )
        );

        assert_eq!(
            Type::forall(Var(2)).whnf(Subst::cons(
                Type::closure(Var(0), Id),
                Subst::comp(Subst::cons(Type::closure(Var(0), Id), Shift), Shift)
            )),
            (
                Type::forall(Var(2)),
                Subst::cons(
                    Type::closure(Var(0), Id),
                    Subst::comp(Subst::cons(Type::closure(Var(0), Id), Shift), Shift)
                )
            )
        );

        assert_eq!(
            Var(0).whnf(Subst::comp(
                Subst::comp(Subst::cons(Type::closure(Var(0), Id), Shift), Shift),
                Shift
            )),
            (Var(2), Id)
        );

        assert_eq!(
            Var(1).whnf(Subst::comp(
                Subst::cons(
                    Type::closure(Var(0), Id),
                    Subst::comp(Subst::cons(Type::closure(Var(0), Id), Shift), Shift)
                ),
                Shift
            )),
            (Var(2), Id)
        );

        assert_eq!(
            Var(2).whnf(Subst::cons(
                Type::closure(Var(0), Id),
                Subst::comp(
                    Subst::cons(
                        Type::closure(Var(0), Id),
                        Subst::comp(Subst::cons(Type::closure(Var(0), Id), Shift), Shift)
                    ),
                    Shift
                )
            )),
            (Var(2), Id)
        );
    }

    #[bench]
    fn bench_nf(b: &mut Bencher) {
        use self::Subst::*;
        use self::Type::*;
        b.iter(|| Var(0).nf(Subst::comp(Shift, Shift)));
    }

    #[bench]
    fn bench_subst_top_1(b: &mut Bencher) {
        use self::Subst::*;
        use self::Type::*;
        b.iter(|| Var(0).nf(Subst::cons(Type::closure(Var(0), Id), Id)));
    }

    #[bench]
    fn bench_subst_top_2(b: &mut Bencher) {
        use self::Subst::*;
        use self::Type::*;
        fn f(n: usize) -> Type {
            let mut t = Var(0);
            for _ in 0..n {
                t = Type::arr(Var(0), t)
            }
            t
        }
        let big = f(100);
        let s = Subst::cons(Type::closure(big, Id), Id);
        b.iter(|| Var(0).nf(s.clone()));
    }

    #[bench]
    fn bench_subst_top_3(b: &mut Bencher) {
        use self::Subst::*;
        use self::Type::*;
        fn f(n: usize) -> Type {
            let mut t = Var(0);
            for _ in 0..n {
                t = Type::arr(Var(0), t)
            }
            t
        }
        let big = f(100);
        let s = Subst::cons(Type::closure(big.clone(), Id), Id);
        b.iter(|| big.clone().nf(s.clone()));
    }
}
