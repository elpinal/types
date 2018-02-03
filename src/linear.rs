/// A linear type system.

use std::cmp::Ordering;
use std::iter::Iterator;
use std::ops::Div;

use context::Ctx;

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

#[derive(PartialEq, Clone)]
struct Type(Qual, Box<Pretype>);

#[derive(PartialEq, Clone)]
enum Pretype {
    Bool,
    Pair(Type, Type),
    Arr(Type, Type),
}

#[derive(Clone, PartialEq)]
struct Context(Vec<Type>);

macro_rules! context {
    ( $( $x:expr ),* ) => {
        {
            let mut v = Vec::new();
            $(
                v.push($x);
             )*
                Context(v)
        }
    }
}

trait TypeCheck {
    type Type;
    type Ctx;

    fn type_of(&self, ctx: &mut Self::Ctx) -> Option<Self::Type>;
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

//impl Iterator for Context {
//    type Item = Type;
//    /// Returns a type which the most recently bound variable has.
//    fn next(&mut self) -> Option<Self::Item> {
//        self.0.pop()
//    }
//}

impl Div for Context {
    type Output = Option<Context>;

    fn div(mut self, ctx: Self) -> Self::Output {
        self.div_mut(ctx)?;
        Some(self)
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

    fn remove(&mut self, x: usize) {
        self.0.remove(x);
    }

    fn push(&mut self, t: Type) {
        self.0.push(t);
    }

    fn pop(&mut self) -> Option<Type> {
        self.0.pop()
    }

    fn div_mut(&mut self, mut ctx: Self) -> Option<()> {
        use self::Qual::*;
        if ctx.is_empty() {
            return Some(());
        }
        match ctx.pop()? {
            x @ Type(Linear, _) => {
                if ctx.contains(&x) {
                    self.div_mut(ctx)
                } else {
                    None
                }
            }
            x @ Type(Unrestricted, _) => {
                self.div_mut(ctx)?;
                let i = Context::position(self, &x)?;
                self.remove(i);
                Some(())
            }
        }
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

    fn type_of(&self, ctx: &mut Context) -> Option<Type> {
        use self::Qual::*;
        use self::Term::*;
        match *self {
            Var(x, _) => Term::type_of_var(x, ctx),
            Bool(q, _) => Some(qual!(q, Pretype::Bool)),
            If(ref t1, ref t2, ref t3) => Term::type_of_if(t1, t2, t3, ctx),
            Pair(q, ref t1, ref t2) => Term::type_of_pair(q, t1, t2, ctx),
            Split(ref t1, ref t2) => Term::type_of_split(t1, t2, ctx),
            Abs(q, ref ty, ref t) => Term::type_of_abs(q, ty, t, ctx),
            App(ref t1, ref t2) => Term::type_of_app(t1, t2, ctx),
        }
    }
}

impl Term {
    fn type_of_var(x: usize, ctx: &mut Context) -> Option<Type> {
        let Type(q, pt) = ctx.get(x)?.clone();
        match q {
            Unrestricted => Some(Type(q, pt)),
            Linear => {
                ctx.remove(x);
                Some(Type(q, pt))
            }
        }
    }

    fn type_of_if(t1: &Term, t2: &Term, t3: &Term, ctx: &mut Context) -> Option<Type> {
        let pt = t1.type_of(ctx)?.pretype();
        if pt != Pretype::Bool {
            return None;
        }
        let ty2 = t2.type_of(ctx)?;
        let mut ctx1 = ctx.clone();
        let ty3 = t3.type_of(&mut ctx1)?;
        // TODO:
        // On Linear type system, since contexts have the exchange property, the
        // equality check for two contexts might need consider it. Need investigation.
        if *ctx != ctx1 || ty2 != ty3 {
            None
        } else {
            Some(ty2)
        }
    }

    fn type_of_pair(q: Qual, t1: &Term, t2: &Term, ctx: &mut Context) -> Option<Type> {
        let ty1 = t1.type_of(ctx)?;
        let ty2 = t2.type_of(ctx)?;
        if !(ty1.can_appear_in(q) && ty2.can_appear_in(q)) {
            return None;
        }
        Some(qual!(q, Pretype::Pair(ty1, ty2)))
    }

    fn type_of_split(t1: &Term, t2: &Term, ctx: &mut Context) -> Option<Type> {
        let pt1 = t1.type_of(ctx)?.pretype();
        if let Pretype::Pair(ty11, ty12) = pt1 {
            ctx.push(ty11.clone());
            ctx.push(ty12.clone());
            let ty2 = t2.type_of(ctx)?;
            ctx.div_mut(context![ty11, ty12])?;
            Some(ty2)
        } else {
            None
        }
    }

    fn type_of_abs(q: Qual, ty1: &Type, t: &Term, ctx: &mut Context) -> Option<Type> {
        let mut ctx1 = ctx.clone();
        ctx1.push(ty1.clone());
        let ty2 = t.type_of(&mut ctx1)?;
        if q == Qual::Unrestricted {
            ctx1.div_mut(context![ty1.clone()])?;
            if *ctx != ctx1 {
                return None;
            }
        }
        ctx.div_mut(context![ty1.clone()])?;
        Some(qual!(q, Pretype::Arr(ty1.clone(), ty2)))
    }

    fn type_of_app(t1: &Term, t2: &Term, ctx: &mut Context) -> Option<Type> {
        use self::Pretype::*;
        let ty1 = t1.type_of(ctx)?;
        let ty2 = t2.type_of(ctx)?;
        match ty1 {
            Type(_, pt) => {
                let pt = *pt;
                match pt {
                    Arr(ty11, ty12) => if ty11 != ty2 { None } else { Some(ty12) },
                    _ => None,
                }
            }
        }
    }
}

impl Type {
    fn pretype(self) -> Pretype {
        *self.1
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
