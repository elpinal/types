/// A linear type system.

use std::cmp::Ordering;
use std::iter::Iterator;
use std::ops::Div;

#[derive(Clone, Copy, PartialEq)]
enum Qual {
    Linear,
    Unrestricted,
}

enum Term {
    Var(usize, usize),
    Bool(Qual, Bool),
    If(Box<Term>, Box<Term>, Box<Term>),
    Pair(Qual, Box<Term>, Box<Term>),
    Split(Box<Term>, Box<Term>),
    Abs(Qual, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

enum Bool {
    True,
    False,
}

#[derive(PartialEq)]
struct Type(Qual, Box<Pretype>);

#[derive(PartialEq)]
enum Pretype {
    Bool,
    Pair(Type, Type),
    Arr(Type, Type),
}

struct Context(Vec<Type>);

trait TypeCheck {
    type Type;
    type Ctx;

    fn type_of(&self, ctx: &Self::Ctx) -> Self::Type;
}

impl PartialOrd for Qual {
    fn partial_cmp(&self, q: &Self) -> Option<Ordering> {
        use self::Qual::*;
        use self::Ordering::*;
        if *self == Unrestricted && *q == Linear {
            return Some(Greater);
        }
        if *self == Linear && *q == Unrestricted {
            return Some(Less);
        }
        if self == q { Some(Equal) } else { None }
    }
}

trait Containment {
    fn can_appear_in(&self, q: Qual) -> bool;
}

impl Containment for Type {
    fn can_appear_in(&self, q1: Qual) -> bool {
        let Type(q2, _) = *self;
        q1 <= q2
    }
}

impl Containment for Context {
    fn can_appear_in(&self, q: Qual) -> bool {
        self.0.iter().all(|ty| ty.can_appear_in(q))
    }
}

impl Iterator for Context {
    type Item = Type;
    /// Returns a type which the most recently bound variable has.
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

impl Div for Context {
    type Output = Option<Context>;

    fn div(self, mut ctx: Self) -> Self::Output {
        use self::Qual::*;
        if ctx.is_empty() {
            return Some(self);
        }
        match ctx.next()? {
            x @ Type(Linear, _) => {
                if ctx.contains(&x) {
                    self.div(ctx)
                } else {
                    None
                }
            }
            x @ Type(Unrestricted, _) => {
                let mut ctx1 = self.div(ctx)?;
                let i = ctx1.position(&x)?;
                let mut ctx2 = ctx1.split_off(i);
                ctx1.append(&mut ctx2);
                return Some(ctx1);
            }
        }
    }
}

impl Context {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn contains(&self, t: &Type) -> bool {
        self.0.contains(t)
    }

    fn position(&self, t2: &Type) -> Option<usize> {
        self.0.iter().position(|t1| t1 == t2)
    }

    fn split_off(&mut self, at: usize) -> Self {
        Context(self.0.split_off(at))
    }

    fn append(&mut self, other: &mut Self) {
        self.0.append(&mut other.0);
    }

    fn get(&self, x: usize) -> Option<&Type> {
        self.0.get(x)
    }
}

macro_rules! qual {
    ($q:expr, $t:expr) => {
        Type($q, Box::new($t))
    }
}

impl TypeCheck for Term {
    type Type = Type;
    type Ctx = Context;

    fn type_of(&self, ctx: &Context) -> Self::Type {
        use self::Qual::*;
        use self::Term::*;
        qual!(Unrestricted, Pretype::Bool);
        match *self {
            Var(x, n) => {
                //
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_partial_ord_for_qual() {
        use self::Qual::*;

        assert!(Unrestricted <= Unrestricted);
        assert!(Linear <= Unrestricted);
        assert!(Linear <= Linear);

        assert!(Unrestricted >= Unrestricted);
        assert!(!(Linear >= Unrestricted));
        assert!(Linear >= Linear);

        assert!(!(Unrestricted <= Linear));
    }
}
