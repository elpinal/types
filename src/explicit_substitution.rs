//! Explicit substitution.

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
    Cons(Box<Type>, Box<Subst>),
    Comp(Box<Subst>, Box<Subst>),
}

impl Type {
    fn whnf(self, s0: Subst) -> (Type, Subst) {
        use self::Subst::*;
        use self::Type::*;
        match self {
            Var(n) => match s0 {
                Id => (Var(n), Id),
                Shift => (Var(n + 1), Id),
                Cons(t, s) => {
                    if n == 0 {
                        let t = *t;
                        match t {
                            Closure(t, s) => t.whnf(s),
                            _ => panic!("unexpected error"),
                        }
                    } else {
                        Var(n - 1).whnf(*s)
                    }
                }
                Comp(s1, s2) => Closure(Box::new(self), *s1).whnf(*s2),
            },
            Closure(t, s) => {
                match *t {
                    Var(n) => {
                        match s {
                            Id => Var(n).whnf(s0),
                            Shift => Var(n + 1).whnf(s0),
                            Cons(t1, s1) => {
                                if n == 0 {
                                    t1.whnf(s0)
                                } else {
                                    Var(n - 1).whnf(*s1)
                                }
                            }
                            Comp(s1, s2) => Closure(t, *s1).whnf(Comp(s2, Box::new(s0))),
                        }
                    }
                    _ => t.whnf(Subst::comp(s, s0)),
                }
            }
            _ => (self, s0),
        }
    }
}

impl Subst {
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
mod tests {}
