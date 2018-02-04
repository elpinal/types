//! A linear type system.
#![warn(dead_code)]

use std::cmp::Ordering;
use std::iter::Iterator;
use std::result;

use context::Ctx;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Qual {
    Linear,
    Unrestricted,
}

#[derive(Debug)]
pub enum Term {
    Var(usize, usize),
    Bool(Qual, Bool),
    If(Box<Term>, Box<Term>, Box<Term>),
    Pair(Qual, Box<Term>, Box<Term>),
    Split(Box<Term>, Box<Term>),
    Abs(Qual, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

#[derive(Debug)]
pub enum Bool {
    True,
    False,
}

#[derive(PartialEq, Clone, Debug)]
pub struct Type(Qual, Box<Pretype>);

#[derive(PartialEq, Clone, Debug)]
pub enum Pretype {
    Bool,
    Pair(Type, Type),
    Arr(Type, Type),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Context(Vec<Option<Type>>);

struct Iter<'a>(&'a Vec<Option<Type>>, usize);

pub trait TypeCheck {
    type Output;
    type Ctx;

    fn type_of(&self, ctx: &mut Self::Ctx) -> Self::Output;
}

#[derive(Debug, PartialEq)]
pub enum Error {
    Undefined(usize, Context),
    TypeMismatch(Type, Type),
    PretypeMismatch(Pretype, Pretype),
    ContextMismatch(Context, Context),
    ExpectArrow(Pretype),
    ExpectPair(Pretype),
    Containment(Qual, Type, Type),
    UnusedLinear(usize),
}

type Result<T> = result::Result<T, Error>;

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
        self.iter().all(|ty| ty.can_appear_in(q))
    }
}

impl Context {
    fn iter(&self) -> Iter {
        Iter(&self.0, self.0.len())
    }

    fn len(&self) -> usize {
        self.iter().count()
    }

    fn get(&self, x: usize) -> Option<&Type> {
        match self.0.get(self.index_from_outermost(x)?) {
            Some(x) => {
                match x {
                    &Some(ref ty) => Some(ty),
                    _ => None,
                }
            }
            None => None,
        }
    }

    fn index_from_outermost(&self, x: usize) -> Option<usize> {
        self.0.len().checked_sub(x + 1)
    }

    fn remove(&mut self, x: usize) {
        let at = self.index_from_outermost(x).expect(&format!(
            "index out of range: {}",
            x
        ));
        self.0[at] = None;
    }

    fn push(&mut self, t: Type) {
        self.0.push(Some(t));
    }

    fn pop(&mut self) -> Option<Type> {
        loop {
            if let Some(ty) = self.0.pop()? {
                return Some(ty);
            }
        }
    }

    fn trancate(&mut self, l: usize, qs: &[Qual]) -> Result<()> {
        use self::Qual::*;
        let uns = qs.iter().fold(
            0,
            |x, &q| if q == Unrestricted { x + 1 } else { x },
        );
        if self.len() != l + uns {
            // Some of linear variables did not used.
            return Err(Error::UnusedLinear(qs.len() - uns));
        }
        for _ in 0..uns {
            let _ = self.pop().expect("trancate: unexpected error");
        }
        Ok(())
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Type;

    fn next(&mut self) -> Option<&'a Type> {
        while 0 < self.1 {
            self.1 -= 1;
            if let Some(ref ty) = self.0[self.1] {
                return Some(ty);
            }
        }
        None
    }
}

macro_rules! qual {
    ($q:expr, $t:expr) => {
        Type($q, Box::new($t))
    }
}

impl TypeCheck for Term {
    type Output = Result<Type>;
    type Ctx = Context;

    fn type_of(&self, ctx: &mut Context) -> Result<Type> {
        use self::Term::*;
        match *self {
            Var(x, _) => Term::type_of_var(x, ctx),
            Bool(q, _) => Ok(qual!(q, Pretype::Bool)),
            If(ref t1, ref t2, ref t3) => Term::type_of_if(t1, t2, t3, ctx),
            Pair(q, ref t1, ref t2) => Term::type_of_pair(q, t1, t2, ctx),
            Split(ref t1, ref t2) => Term::type_of_split(t1, t2, ctx),
            Abs(q, ref ty, ref t) => Term::type_of_abs(q, ty, t, ctx),
            App(ref t1, ref t2) => Term::type_of_app(t1, t2, ctx),
        }
    }
}

impl Term {
    fn type_of_var(x: usize, ctx: &mut Context) -> Result<Type> {
        let Type(q, pt) = ctx.get(x).cloned().ok_or_else(
            || Error::Undefined(x, ctx.clone()),
        )?;
        if q == Qual::Linear {
            ctx.remove(x);
        }
        Ok(Type(q, pt))
    }

    fn type_of_if(t1: &Term, t2: &Term, t3: &Term, ctx: &mut Context) -> Result<Type> {
        use self::Pretype::*;
        let pt = t1.type_of(ctx)?.pretype();
        if pt != Bool {
            return Err(Error::PretypeMismatch(pt, Bool));
        }
        let mut ctx1 = ctx.clone();
        let ty2 = t2.type_of(ctx)?;
        let ty3 = t3.type_of(&mut ctx1)?;
        // TODO:
        // On Linear type system, since contexts have the exchange property, the
        // equality check for two contexts might need consider it. Need investigation.
        if *ctx != ctx1 {
            Err(Error::ContextMismatch(ctx.clone(), ctx1))
        } else if ty2 != ty3 {
            Err(Error::TypeMismatch(ty3, ty2))
        } else {
            Ok(ty2)
        }
    }

    fn type_of_pair(q: Qual, t1: &Term, t2: &Term, ctx: &mut Context) -> Result<Type> {
        let ty1 = t1.type_of(ctx)?;
        let ty2 = t2.type_of(ctx)?;
        if !(ty1.can_appear_in(q) && ty2.can_appear_in(q)) {
            return Err(Error::Containment(q, ty1, ty2));
        }
        Ok(qual!(q, Pretype::Pair(ty1, ty2)))
    }

    fn type_of_split(t1: &Term, t2: &Term, ctx: &mut Context) -> Result<Type> {
        let (ty11, ty12) = t1.type_of(ctx)?.pretype().pair().map_err(
            |pt| Error::ExpectPair(pt),
        )?;
        let l = ctx.len();
        let q1 = ty11.qual();
        let q2 = ty12.qual();
        ctx.push(ty11);
        ctx.push(ty12);
        let ty2 = t2.type_of(ctx)?;
        ctx.trancate(l, &[q1, q2])?;
        Ok(ty2)
    }

    fn type_of_abs(q: Qual, ty1: &Type, t: &Term, ctx: &mut Context) -> Result<Type> {
        let l = ctx.len();
        ctx.push(ty1.clone());
        let ty2 = t.type_of(ctx)?;
        ctx.trancate(l, &[ty1.qual()])?;
        Ok(qual!(q, Pretype::Arr(ty1.clone(), ty2)))
    }

    fn type_of_app(t1: &Term, t2: &Term, ctx: &mut Context) -> Result<Type> {
        let ty1 = t1.type_of(ctx)?;
        let ty2 = t2.type_of(ctx)?;
        match ty1.pretype() {
            Pretype::Arr(ty11, ty12) => {
                if ty11 == ty2 {
                    return Ok(ty12);
                }
                return Err(Error::TypeMismatch(ty2, ty11));
            }
            pt => Err(Error::ExpectArrow(pt)),
        }
    }

    fn abs(q: Qual, ty: Type, t: Term) -> Term {
        Term::Abs(q, ty, Box::new(t))
    }

    fn app(t1: Term, t2: Term) -> Term {
        Term::App(Box::new(t1), Box::new(t2))
    }
}

impl Type {
    fn qual(&self) -> Qual {
        self.0
    }

    fn pretype(self) -> Pretype {
        *self.1
    }
}

impl Pretype {
    fn pair(self) -> result::Result<(Type, Type), Pretype> {
        if let Pretype::Pair(t1, t2) = self {
            Ok((t1, t2))
        } else {
            Err(self)
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

    macro_rules! context {
        () => ( Context(Vec::new()) );

        ( $( $x:expr ),* ) => {
            {
                let mut v = Vec::new();
                $(
                    v.push(Some($x));
                )*
                Context(v)
            }
        }
    }

    #[test]
    fn test_context_index() {
        let ctx = Context(vec![Some(qual!(Qual::Linear, Pretype::Bool)), None]);
        assert_eq!(ctx.index_from_outermost(1), Some(0));
    }

    #[test]
    fn test_context_trancate() {
        use self::Qual::*;
        use self::Pretype::*;

        let mut ctx = context![qual!(Linear, Bool)];
        assert!(ctx.trancate(1, &[Linear]).is_ok());

        let mut ctx = context![qual!(Linear, Bool)];
        assert!(ctx.trancate(0, &[Linear]).is_err());

        let mut ctx = context![qual!(Linear, Bool)];
        assert!(ctx.trancate(0, &[Unrestricted]).is_ok());

        let mut ctx = context![qual!(Unrestricted, Bool)];
        assert!(ctx.trancate(0, &[Unrestricted]).is_ok());

        let mut ctx = context![qual!(Unrestricted, Bool), qual!(Unrestricted, Bool)];
        assert!(ctx.trancate(0, &[Unrestricted]).is_err());

        let mut ctx = context![qual!(Unrestricted, Bool), qual!(Unrestricted, Bool)];
        assert!(ctx.trancate(1, &[Unrestricted]).is_ok());
    }

    macro_rules! assert_type {
        ($t:expr, [ $( $x:expr ),* ], $ty:expr) => {
            {
                let mut ctx = context![$( $x ),*];
                assert_eq!($t.type_of(&mut ctx), $ty);
            }
        }
    }

    macro_rules! typable {
        ($t:expr, [ $( $x:expr ),* ], $ty:expr) => {
            { assert_type!($t, [$( $x ),*], Some($ty)); }
        }
    }

    macro_rules! not_typable {
        ($t:expr, [ $( $x:expr ),* ]) => {
            { assert_type!($t, [$( $x ),*], None); }
        }
    }

    #[test]
    fn test_typecheck() {
        use self::Bool::*;
        use self::Qual::*;
        use self::Term::*;

        typable!(
            Bool(Unrestricted, True),
            [],
            qual!(Unrestricted, Pretype::Bool)
        );

        typable!(
            Bool(Unrestricted, True),
            [qual!(Unrestricted, Pretype::Bool)],
            qual!(Unrestricted, Pretype::Bool)
        );

        typable!(Bool(Linear, True), [], qual!(Linear, Pretype::Bool));

        not_typable!(Var(0, 1), [], Error::Undefined(0, context![]));
        typable!(
            Var(0, 1),
            [qual!(Linear, Pretype::Bool)],
            qual!(Linear, Pretype::Bool)
        );

        not_typable!(
            Term::app(Var(0, 1), Var(0, 1)),
            [qual!(Linear, Pretype::Bool)],
            Error::Undefined(0, Context(vec![None]))
        );
        not_typable!(
            Term::app(Var(0, 1), Var(0, 1)),
            [qual!(Unrestricted, Pretype::Bool)],
            Error::ExpectArrow(Pretype::Bool)
        );
        typable!(
            Term::app(Var(0, 2), Var(1, 2)),
            [
                qual!(Unrestricted, Pretype::Bool),
                qual!(
                    Unrestricted,
                    Pretype::Arr(
                        qual!(Unrestricted, Pretype::Bool),
                        qual!(Unrestricted, Pretype::Bool),
                    )
                ),
            ],
            qual!(Unrestricted, Pretype::Bool)
        );
    }
}
