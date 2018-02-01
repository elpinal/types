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

struct Type(Qual, Box<Pretype>);

enum Pretype {
    Bool,
    Pair(Type, Type),
    Arr(Type, Type),
}

struct Context(Vec<Type>);

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

    fn div(self, ctx: Self) -> Self::Output {
        use self::Qual::*;
        if ctx.is_empty() {
            return Some(self);
        }
        match ctx.next()? {
            Type(Linear, _) as x => {
                if ctx.contains(&x) {
                    return self.div(ctx);
                }
            }
            Type(Unrestricted, _) as x => {
                let ctx1 = self.div(ctx)?;
                let i = ctx1.position(x);
                if let (mut ctx2, ctx3) = ctx1.split_off(i) {
                    ctx2.append(ctx3);
                    return Some(ctx2);
                }
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
