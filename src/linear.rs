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

#[derive(Clone, Debug, PartialEq)]
pub struct Value(Qual, Prevalue);

#[derive(Clone, Debug, PartialEq)]
enum Prevalue {
    Bool(Bool),
    Pair(usize, usize),
    Abs(Type, Term),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Store {
    stack: Vec<Option<Value>>,
    heap: Vec<Option<Value>>,
}

pub trait TypeCheck {
    type Output;
    type Ctx;

    fn type_of(&self, ctx: &mut Self::Ctx) -> Self::Output;
}

#[derive(Debug, PartialEq)]
pub enum TypeError {
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

type Result<T> = result::Result<T, TypeError>;

#[derive(Debug, PartialEq)]
pub enum EvalError {
    Undefined(usize, Store),
    NotAbs(Value),
    NotPair(Value),
    NotBool(Value),
}

type EvalResult<T> = result::Result<T, EvalError>;

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
                        return Err(TypeError::UnusedLinear(ty));
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
            || TypeError::Undefined(x, ctx.clone()),
        )?;
        if q == Qual::Linear {
            ctx.remove(x);
        }
        Ok(Type(q, pt))
    }

    fn type_of_if(t1: &Term, t2: &Term, t3: &Term, ctx: &mut Context) -> Result<Type> {
        use self::Pretype::*;
        use self::TypeError::*;
        let pt = t1.type_of(ctx)?.pretype();
        if pt != Bool {
            return Err(PretypeMismatch(pt, Bool));
        }
        let mut ctx1 = ctx.clone();
        let ty2 = t2.type_of(ctx)?;
        let ty3 = t3.type_of(&mut ctx1)?;
        // TODO:
        // On Linear type system, since contexts have the exchange property, the
        // equality check for two contexts might need consider it. Need investigation.
        if *ctx != ctx1 {
            Err(ContextMismatch(ctx.clone(), ctx1))
        } else if ty2 != ty3 {
            Err(TypeMismatch(ty3, ty2))
        } else {
            Ok(ty2)
        }
    }

    fn type_of_pair(q: Qual, t1: &Term, t2: &Term, ctx: &mut Context) -> Result<Type> {
        let ty1 = t1.type_of(ctx)?;
        let ty2 = t2.type_of(ctx)?;
        if !(ty1.can_appear_in(q) && ty2.can_appear_in(q)) {
            return Err(TypeError::Containment(q, ty1, ty2));
        }
        Ok(qual!(q, Pretype::Pair(ty1, ty2)))
    }

    fn type_of_split(t1: &Term, t2: &Term, ctx: &mut Context) -> Result<Type> {
        let (ty11, ty12) = t1.type_of(ctx)?.pretype().pair().map_err(|pt| {
            TypeError::ExpectPair(pt)
        })?;
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
            return Err(TypeError::LinearInUnAbs(ctx.clone()));
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
                Err(TypeError::TypeMismatch(ty2, ty11))
            }
            pt => Err(TypeError::ExpectArrow(pt)),
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

    fn split(t1: Term, t2: Term) -> Term {
        Term::Split(Box::new(t1), Box::new(t2))
    }

    /// Evaluates a term.
    fn eval(self) -> EvalResult<(Value, Store)> {
        self.eval_store(Store::new())
    }

    /// Evaluates with an initial store.
    fn eval_store(self, mut s: Store) -> EvalResult<(Value, Store)> {
        use self::Term::*;
        use self::Bool::*;
        use self::EvalError::*;
        match self {
            Bool(q, b) => Ok((Value(q, Prevalue::Bool(b)), s)),
            If(t1, t2, t3) => {
                let (v1, s) = t1.eval_store(s)?;
                let (q, b) = v1.bool().map_err(|v| NotBool(v))?;
                match b {
                    True => t2.eval_store(s),
                    False => t3.eval_store(s),
                }
            }
            Pair(q, t1, t2) => {
                let (v1, mut s1) = t1.eval()?;
                let (v2, mut s2) = t2.eval()?;
                s1.append(&mut s2);
                let x = s1.add(v1);
                let y = s1.add(v2);
                Ok((Value(q, Prevalue::Pair(x, y)), s1))
            }
            Split(t1, t2) => {
                let (v1, mut s1) = t1.eval()?;
                let (q, x, y) = v1.pair().map_err(|v| NotPair(v))?;
                s1.move_top(x);
                s1.move_top(y);
                let (v2, mut s2) = t2.eval_store(s1)?;
                s2.pop_times_expect(2, "eval_store: Split");
                Ok((v2, s2))
            }
            Abs(q, ty, t) => Ok((Value(q, Prevalue::Abs(ty, *t)), s)),
            App(t1, t2) => {
                let (v1, s1) = t1.eval()?;
                let (q, _, t) = v1.abs().map_err(|v| NotAbs(v))?;
                let (v2, s2) = t2.eval()?;
                let mut s0 = Store::new();
                s0.push(v2);
                let (v, mut s) = t.eval_store(s0)?;
                s.pop_times_expect(1, "eval_store: function application");
                Ok((v, s))
            }
            Var(x, n) => {
                let v = s.get(x).ok_or_else(|| Undefined(x, s.clone()))?;
                Ok((v, s))
            }
        }
    }

    fn map_ref<F>(&mut self, onvar: &F, c: usize)
    where
        F: Fn(usize, usize, usize, &mut Self),
    {
        use self::Term::*;
        let f = |ts: &mut [&mut Term]| ts.iter_mut().for_each(|t| t.map_ref(onvar, c));
        match *self {
            Var(x, n) => onvar(c, x, n, self),
            Bool(..) => (),
            If(ref mut t1, ref mut t2, ref mut t3) => f(&mut [t1, t2, t3]),
            Pair(_, ref mut t1, ref mut t2) => f(&mut [t1, t2]),
            Split(ref mut t1, ref mut t2) => {
                [(0, t1), (2, t2)].iter_mut().for_each(
                    |&mut (i, ref mut t)| {
                        t.map_ref(onvar, c + i)
                    },
                )
            }
            Abs(_, _, ref mut t) => t.map_ref(onvar, c + 1),
            App(ref mut t1, ref mut t2) => f(&mut [t1, t2]),
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
    fn qual(&self) -> Qual {
        self.0
    }

    fn bool(self) -> result::Result<(Qual, Bool), Self> {
        match self.1 {
            Prevalue::Bool(b) => Ok((self.0, b)),
            _ => Err(self),
        }
    }

    fn pair(self) -> result::Result<(Qual, usize, usize), Self> {
        match self.1 {
            Prevalue::Pair(t1, t2) => Ok((self.0, t1, t2)),
            _ => Err(self),
        }
    }

    fn abs(self) -> result::Result<(Qual, Type, Term), Self> {
        match self.1 {
            Prevalue::Abs(ty, t) => Ok((self.0, ty, t)),
            _ => Err(self),
        }
    }
}

impl Store {
    fn new() -> Store {
        Store {
            stack: vec![],
            heap: vec![],
        }
    }

    fn push(&mut self, v: Value) {
        self.stack.push(Some(v));
    }

    fn pop(&mut self) -> Option<Value> {
        self.stack.pop()?
    }

    fn pop_times(&mut self, n: usize) -> Option<()> {
        for _ in 0..n {
            self.pop()?;
        }
        Some(())
    }

    fn pop_times_expect(&mut self, n: usize, msg: &str) {
        self.pop_times(n).expect(&format!(
            "{}: unexpectedly small Store: {:?}",
            msg,
            self
        ));
    }

    fn add(&mut self, v: Value) -> usize {
        self.heap.push(Some(v));
        self.heap.len() - 1
    }

    fn append(&mut self, s: &mut Store) {
        self.stack.append(&mut s.stack);
        self.heap.append(&mut s.heap);
    }

    fn index_from_top(&self, x: usize) -> Option<usize> {
        self.stack.len().checked_sub(x + 1)
    }

    fn get(&mut self, x: usize) -> Option<Value> {
        self.stack.get(self.index_from_top(x)?).cloned()?
    }

    fn move_top(&mut self, x: usize) -> Option<()> {
        let v = self.heap.get(x).cloned()??;
        self.heap[x] = None;
        self.push(v);
        Some(())
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
        use self::TypeError::*;

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

        not_typable!(Var(0, 1), [], Undefined(0, context![]));
        typable!(
            Var(0, 1),
            [qual!(Linear, Pretype::Bool)],
            qual!(Linear, Pretype::Bool)
        );

        not_typable!(
            Term::app(Var(0, 1), Var(0, 1)),
            [qual!(Linear, Pretype::Bool)],
            Undefined(0, Context(vec![None]))
        );
        not_typable!(
            Term::app(Var(0, 1), Var(0, 1)),
            [qual!(Unrestricted, Pretype::Bool)],
            ExpectArrow(Pretype::Bool)
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

        typable!(
            Term::split(
                Term::pair(Linear, Bool(Unrestricted, False), Bool(Unrestricted, True)),
                Bool(Linear, True),
            ),
            [],
            qual!(Linear, Pretype::Bool)
        );

        not_typable!(
            Term::split(
                Term::pair(Linear, Bool(Linear, False), Bool(Unrestricted, True)),
                Bool(Linear, True),
            ),
            [],
            UnusedLinear(qual!(Linear, Pretype::Bool))
        );

        typable!(
            Term::split(
                Term::pair(Linear, Bool(Unrestricted, False), Bool(Unrestricted, True)),
                Term::conditional(Var(1, 2), Bool(Linear, False), Bool(Linear, True)),
            ),
            [],
            qual!(Linear, Pretype::Bool)
        );
    }

    macro_rules! assert_eval {
        ($t:expr, $result:expr) => {
            assert_eq!($t.eval(), $result);
        }
    }

    macro_rules! store {
        ( $($x:expr),* ) => ( Store{stack: vec![$(Some($x)),*], heap: vec![]} );
        ( $($x:expr,)* ) => ( store![$($x),*] );
    }

    macro_rules! store_heap {
        ( $($x:expr),* ) => ( Store{heap: vec![$(Some($x)),*], stack: vec![]} );
        ( $($x:expr,)* ) => ( store_heap![$($x),*] );
    }

    #[test]
    fn test_eval() {
        use self::Term::*;
        use self::Bool::*;
        use self::Qual::*;

        assert_eval!(
            Bool(Unrestricted, True),
            Ok((Value(Unrestricted, Prevalue::Bool(True)), Store::new()))
        );

        assert_eval!(
            Bool(Linear, True),
            Ok((Value(Linear, Prevalue::Bool(True)), Store::new()))
        );

        assert_eval!(
            Term::conditional(
                Bool(Unrestricted, True),
                Bool(Linear, True),
                Bool(Linear, False),
            ),
            Ok((Value(Linear, Prevalue::Bool(True)), Store::new()))
        );

        assert_eval!(
            Term::conditional(
                Bool(Unrestricted, False),
                Bool(Linear, True),
                Bool(Linear, False),
            ),
            Ok((Value(Linear, Prevalue::Bool(False)), Store::new()))
        );

        assert_eval!(
            Term::conditional(
                Bool(Linear, False),
                Bool(Linear, True),
                Bool(Unrestricted, False),
            ),
            Ok((Value(Unrestricted, Prevalue::Bool(False)), Store::new()))
        );

        assert_eval!(
            Term::pair(Linear, Bool(Unrestricted, False), Bool(Unrestricted, True)),
            Ok((
                Value(Linear, Prevalue::Pair(0, 1)),
                store_heap![
                    Value(Unrestricted, Prevalue::Bool(False)),
                    Value(Unrestricted, Prevalue::Bool(True)),
                ],
            ))
        );

        assert_eval!(
            Term::split(
                Term::pair(Linear, Bool(Unrestricted, False), Bool(Unrestricted, True)),
                Bool(Linear, True),
            ),
            Ok((
                Value(Linear, Prevalue::Bool(True)),
                Store {
                    stack: vec![],
                    heap: vec![None, None],
                },
            ))
        );

        assert_eval!(
            Term::split(
                Term::pair(Linear, Bool(Unrestricted, False), Bool(Unrestricted, True)),
                Var(0, 2),
            ),
            Ok((
                Value(Unrestricted, Prevalue::Bool(True)),
                Store {
                    stack: vec![],
                    heap: vec![None, None],
                },
            ))
        );

        assert_eval!(
            Term::split(
                Term::pair(Linear, Bool(Linear, False), Bool(Unrestricted, True)),
                Var(1, 2),
            ),
            Ok((
                Value(Linear, Prevalue::Bool(False)),
                Store {
                    stack: vec![],
                    heap: vec![None, None],
                },
            ))
        );

        assert_eval!(
            Term::split(
                Term::pair(Linear, Bool(Unrestricted, False), Bool(Unrestricted, True)),
                Term::conditional(Var(1, 2), Bool(Linear, False), Bool(Linear, True)),
            ),
            Ok((
                Value(Linear, Prevalue::Bool(True)),
                Store {
                    stack: vec![],
                    heap: vec![None, None],
                },
            ))
        );

        assert_eval!(
            Term::app(
                Term::abs(
                    Linear,
                    qual!(Linear, Pretype::Bool),
                    Bool(Unrestricted, True),
                ),
                Bool(Linear, False),
            ),
            Ok((Value(Unrestricted, Prevalue::Bool(True)), Store::new()))
        );

        assert_eval!(
            Term::app(
                Term::abs(Linear, qual!(Linear, Pretype::Bool), Var(0, 1)),
                Bool(Linear, False),
            ),
            Ok((Value(Linear, Prevalue::Bool(False)), Store::new()))
        );

        assert_eval!(
            Term::app(
                Term::abs(
                    Linear,
                    qual!(Linear, Pretype::Bool),
                    Term::abs(Linear, qual!(Linear, Pretype::Bool), Var(1, 2)),
                ),
                Bool(Linear, False),
            ),
            Ok((
                Value(
                    Linear,
                    Prevalue::Abs(qual!(Linear, Pretype::Bool), Var(1, 2)),
                ),
                store![],
            ))
        );
    }
}
