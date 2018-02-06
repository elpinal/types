//! A linear type system.
#![warn(dead_code)]

use std::cmp::Ordering;
use std::iter::Iterator;
use std::result;

use ::*;
use context::Ctx;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Qual {
    Linear,
    Unrestricted,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(usize, usize),
    Bool(Qual, Bool),
    If(Box<Term>, Box<Term>, Box<Term>),
    Pair(Qual, Box<Term>, Box<Term>),
    Split(Box<Term>, Box<Term>),
    Abs(Qual, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

#[derive(Clone, Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
struct Value(Qual, Prevalue);

#[derive(Debug, PartialEq)]
enum Prevalue {
    Bool(Bool),
    Pair(usize, usize),
    Abs(Type, Term),
}

#[derive(Debug, PartialEq)]
struct Store(Vec<Value>);

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
    UnusedLinear(Type),
    LinearInUnAbs(Context),
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

    fn trancate(&mut self, qs: &[Qual]) -> Result<()> {
        use self::Qual::*;
        for q in qs {
            match *q {
                Linear => {
                    if let Some(ty) = self.0.pop().expect("unexpected error") {
                        return Err(Error::UnusedLinear(ty));
                    }
                }
                Unrestricted => {
                    let _ = self.0.pop();
                }
            }
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
        let q1 = ty11.qual();
        let q2 = ty12.qual();
        ctx.push(ty11);
        ctx.push(ty12);
        let ty2 = t2.type_of(ctx)?;
        ctx.trancate(&[q2, q1])?;
        Ok(ty2)
    }

    fn type_of_abs(q: Qual, ty1: &Type, t: &Term, ctx: &mut Context) -> Result<Type> {
        let v: Vec<bool> = ctx.0.iter().map(|ty| ty.is_some()).collect();
        ctx.push(ty1.clone());
        let ty2 = t.type_of(ctx)?;
        ctx.trancate(&[ty1.qual()])?;
        if q == Qual::Unrestricted && ctx.0.iter().enumerate().any(|(x, ty)| v[x] != ty.is_some()) {
            return Err(Error::LinearInUnAbs(ctx.clone()));
        }
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

    fn conditional(t1: Term, t2: Term, t3: Term) -> Term {
        Term::If(Box::new(t1), Box::new(t2), Box::new(t3))
    }

    fn pair(q: Qual, t1: Term, t2: Term) -> Term {
        Term::Pair(q, Box::new(t1), Box::new(t2))
    }

    fn eval(self) -> Option<(Value, Store)> {
        self.eval_store(Store::new())
    }

    fn eval_store(self) -> Option<(Value, Store)> {
        use self::Term::*;
        use self::Bool::*;
        match self {
            Bool(q, b) => Some((Value(q, Prevalue::Bool(b)), Store::new())),
            If(t1, t2, t3) => {
                let (v1, _) = t1.eval()?;
                let (q, b) = v1.bool()?;
                let (v, s) = match b {
                    True => t2.eval(),
                    False => t3.eval(),
                }?;
                Some((v, s))
            }
            Pair(q, t1, t2) => {
                let (v1, mut s1) = t1.eval()?;
                let (v2, mut s2) = t2.eval()?;
                s1.append(&mut s2);
                let x = s1.add(v1);
                let y = s1.add(v2);
                Some((Value(q, Prevalue::Pair(x, y)), s1))
            }
            Split(t1, t2) => {
                let (v1, mut s1) = t1.eval()?;
                let (q, x, y) = v1.pair()?;
                Some((t2.subst(1, x).subst(0, y), Store::new()))
            }
            Abs(q, ty, t) => Some((Value(q, Prevalue::Abs(ty, *t)), Store::new())),
            App(t1, t2) => {
                let (v1, mut s1) = t1.eval()?;
                let (q, ty, t) = v1.abs()?;
                let (v2, mut s2) = t2.eval()?;
                Some((t.subst_top(v2), Store::new()))
            }
            Var(x, n) => {
                unimplemented!();
            }
        }
    }

    fn map_ref<F>(&mut self, onvar: &F, c: usize)
    where
        F: Fn(usize, usize, usize, &mut Self),
    {
        use self::Term::*;
        match *self {
            Var(x, n) => onvar(c, x, n, self),
            Bool(..) => (),
            If(ref t1, ref t2, ref t3) => {
                for t in &[t1, t2, t3] {
                    t.map_ref(onvar, c);
                }
            }
            Pair(_, ref t1, ref t2) => {
                for t in &[t1, t2] {
                    t.map_ref(onvar, c);
                }
            }
            Split(ref t1, ref t2) => {
                for t in &[t1, t2] {
                    t.map_ref(onvar, c);
                }
            }
            Abs(_, _, ref t) => t.map_ref(onvar, c + 1),
            App(ref t1, ref t2) => {
                for t in &[t1, t2] {
                    t.map_ref(onvar, c);
                }
            }
        }
    }
}

impl ShiftRef for Term {
    fn shift_above_ref(&mut self, c: usize, d: isize) {
        use self::Term::*;
        let add_isize = |a, b| (a as isize + b) as usize;
        let f = |c, x, n, t: &mut Term| if x >= c {
            *t = Var(add_isize(x, d), add_isize(n, d));
        } else {
            *t = Var(x, add_isize(n, d))
        };
        self.map_ref(&f, c);
    }
}

impl SubstRef for Term {
    fn subst_ref(&mut self, j: usize, t: &Term) {
        use self::Term::*;
        let f = |j, x, n, t0: &mut Term| if x == j {
            *t0 = t.clone();
        };
        self.map_ref(&f, j);
    }
}

impl Value {
    fn bool(self) -> Option<(Qual, Bool)> {
        match self.1 {
            Prevalue::Bool(b) => Some((self.0, b)),
            _ => None,
        }
    }

    fn pair(self) -> Option<(Qual, usize, usize)> {
        match self.1 {
            Prevalue::Pair(t1, t2) => Some((self.0, t1, t2)),
            _ => None,
        }
    }

    fn abs(self) -> Option<(Qual, Type, Term)> {
        match self.1 {
            Prevalue::Abs(ty, t) => Some((self.0, ty, t)),
            _ => None,
        }
    }
}

impl Store {
    fn new() -> Store {
        Store(vec![])
    }

    fn add(&mut self, v: Value) -> usize {
        self.0.push(v);
        self.0.len()
    }

    fn append(&mut self, s: &mut Store) {
        self.0.append(&mut s.0);
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

    macro_rules! qual_some {
        ($q:expr, $t:expr) => (Some(qual!($q, $t)))
    }

    #[test]
    fn test_context_trancate() {
        use self::Qual::*;
        use self::Pretype::*;

        let mut ctx = Context(vec![qual_some!(Linear, Bool), None]);
        assert!(ctx.trancate(&[Linear]).is_ok());

        let mut ctx = Context(vec![qual_some!(Linear, Bool)]);
        assert!(ctx.trancate(&[Linear]).is_err());

        let mut ctx = Context(vec![qual_some!(Linear, Bool)]);
        assert!(ctx.trancate(&[Unrestricted]).is_ok());

        let mut ctx = Context(vec![qual_some!(Unrestricted, Bool)]);
        assert!(ctx.trancate(&[Unrestricted]).is_ok());

        let mut ctx = Context(vec![
            qual_some!(Unrestricted, Bool),
            qual_some!(Unrestricted, Bool),
        ]);
        assert!(ctx.trancate(&[Unrestricted]).is_ok());
    }

    macro_rules! assert_type {
        ($t:expr, [ $( $x:expr ),* ], $ty:expr) => {
            {
                let mut ctx = context![$( $x ),*];
                assert_eq!($t.type_of(&mut ctx), $ty);
            }
        };

        ($t:expr, [ $( $x:expr, )* ], $ty:expr) => {
            {
                let mut ctx = context![$( $x ),*];
                assert_eq!($t.type_of(&mut ctx), $ty);
            }
        }
    }

    macro_rules! typable {
        ($t:expr, [ $( $x:expr ),* ], $ty:expr) => {
            { assert_type!($t, [$( $x ),*], Ok($ty)); }
        };

        ($t:expr, [ $( $x:expr, )* ], $ty:expr) => {
            { assert_type!($t, [$( $x ),*], Ok($ty)); }
        }
    }

    macro_rules! not_typable {
        ($t:expr, [ $( $x:expr ),* ], $e:expr) => {
            { assert_type!($t, [$( $x ),*], Err($e)); }
        };

        ($t:expr, [ $( $x:expr, )* ], $e:expr) => {
            { assert_type!($t, [$( $x ),*], Err($e)); }
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

        typable!(
            Term::abs(
                Unrestricted,
                qual!(Linear, Pretype::Bool),
                Term::abs(
                    Linear,
                    qual!(
                        Linear,
                        Pretype::Arr(qual!(Linear, Pretype::Bool), qual!(Linear, Pretype::Bool))
                    ),
                    Term::app(Var(0, 2), Var(1, 2)),
                ),
            ),
            [],
            qual!(
                Unrestricted,
                Pretype::Arr(
                    qual!(Linear, Pretype::Bool),
                    qual!(
                        Linear,
                        Pretype::Arr(
                            qual!(
                                Linear,
                                Pretype::Arr(qual!(Linear, Pretype::Bool), qual!(Linear, Pretype::Bool))
                            ),
                            qual!(Linear, Pretype::Bool),
                        )
                    ),
                )
            )
        );
    }

    macro_rules! assert_eval {
        ($t:expr, $result:expr) => {
            assert_eq!($t.eval(), $result);
        }
    }

    macro_rules! store {
        ( $($x:expr),* ) => ( Store(vec![$($x),*]) );
        ( $($x:expr,)* ) => ( Store(vec![$($x),*]) );
    }

    #[test]
    fn test_eval() {
        use self::Term::*;
        use self::Bool::*;
        use self::Qual::*;

        assert_eval!(
            Bool(Unrestricted, True),
            Some((Value(Unrestricted, Prevalue::Bool(True)), Store::new()))
        );

        assert_eval!(
            Bool(Linear, True),
            Some((Value(Linear, Prevalue::Bool(True)), Store::new()))
        );

        assert_eval!(
            Term::conditional(
                Bool(Unrestricted, True),
                Bool(Linear, True),
                Bool(Linear, False),
            ),
            Some((Value(Linear, Prevalue::Bool(True)), Store::new()))
        );

        assert_eval!(
            Term::conditional(
                Bool(Unrestricted, False),
                Bool(Linear, True),
                Bool(Linear, False),
            ),
            Some((Value(Linear, Prevalue::Bool(False)), Store::new()))
        );

        assert_eval!(
            Term::conditional(
                Bool(Linear, False),
                Bool(Linear, True),
                Bool(Unrestricted, False),
            ),
            Some((Value(Unrestricted, Prevalue::Bool(False)), Store::new()))
        );

        assert_eval!(
            Term::pair(Linear, Bool(Unrestricted, False), Bool(Unrestricted, True)),
            Some((
                Value(Linear, Prevalue::Pair(1, 2)),
                store![
                    Value(Unrestricted, Prevalue::Bool(False)),
                    Value(Unrestricted, Prevalue::Bool(True)),
                ],
            ))
        );
    }
}
