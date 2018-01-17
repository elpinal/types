//! Lambda calculus with kinds.
#![warn(missing_docs)]

#[derive(Clone, Debug, PartialEq)]
enum Type {
    Var(usize, usize),
    Abs(String, Kind, Box<Type>),
    App(Box<Type>, Box<Type>),
    Arr(Box<Type>, Box<Type>),
}

#[derive(Clone, Debug, PartialEq)]
enum Kind {
    Star,
    Arr(Box<Kind>, Box<Kind>),
}

#[derive(Clone, Debug, PartialEq)]
struct Context(Vec<(String, Binding)>);

#[derive(Clone, Debug, PartialEq)]
enum Binding {
    Term(Type),
    Type(Kind),
}

#[derive(Clone, Debug, PartialEq)]
enum Term {
    Var(usize, usize),
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

enum TypeError {
    Unbound(usize, Context),
    NotArr(Type),
    Kind(KindError),
    NotStar(Kind),
    Unexpected(Type, Type),
}

enum KindError {
    Unbound(usize, Context),
    Unexpected(Kind, Kind),
    NotArr(Kind),
}

impl From<KindError> for TypeError {
    fn from(e: KindError) -> TypeError {
        TypeError::Kind(e)
    }
}

impl Type {
    fn kind_of(&self, ctx: Context) -> Result<Kind, KindError> {
        use self::Type::*;
        use self::KindError::*;
        match *self {
            Var(x, n) => ctx.get_kind(x).ok_or_else(|| Unbound(x, ctx)),
            Abs(ref i, ref k1, ref t) => {
                let ctx1 = ctx.clone().add(i.clone(), Binding::Type(k1.clone()));
                let k2 = t.kind_of(ctx1)?;
                let x = Kind::Arr(Box::new(k1.clone()), Box::new(k2));
                Ok(x)
            }
            App(ref t1, ref t2) => {
                let k1 = t1.kind_of(ctx.clone())?;
                match k1 {
                    Kind::Arr(k11, k12) => {
                        let k2 = t2.kind_of(ctx.clone())?;
                        if *k11 == k2 {
                            Ok(*k12)
                        } else {
                            Err(Unexpected(k2, *k11))
                        }
                    }
                    _ => Err(NotArr(k1)),
                }
            }
            Arr(ref t1, ref t2) => {
                match t1.kind_of(ctx.clone())? {
                    Kind::Star => {
                        match t2.kind_of(ctx)? {
                            Kind::Star => Ok(Kind::Star),
                            k => Err(Unexpected(k, Kind::Star)),
                        }
                    }
                    k => Err(Unexpected(k, Kind::Star)),
                }
            }
        }
    }

    fn eval_to_arr(self, ctx: Context) -> Type {
        use self::Type::*;
        match self {
            Abs(..) => self,
            Var(..) => self,
            App(t1, t2) => {
                match t1.eval(ctx) {
                    Abs(_, _, t) => t.subst_top(*t2),
                    t1 => App(Box::new(t1), t2),
                }
            }
            Arr(..) => self,
        }
    }

    fn eval(self, ctx: Context) -> Type {
        let mut t0 = self;
        loop {
            match t0.eval1(ctx.clone()) {
                (t, true) => t0 = t,
                (t, false) => return t,
            }
        }
    }

    fn eval1(self, ctx: Context) -> (Type, bool) {
        use self::Type::*;
        let unchanged = |t| (t, false);
        let changed = |t| (t, true);
        match self {
            Abs(..) => unchanged(self),
            Var(..) => unchanged(self),
            App(t1, t2) => {
                macro_rules! app {
                    ($t:expr) => {App(Box::new($t), t2)}
                }
                match t1.eval1(ctx) {
                    (t, true) => changed(app!(t)),
                    (Abs(i, k, t), false) => changed(t.subst_top(*t2)),
                    (t, false) => unchanged(app!(t)),
                }
            }
            Arr(t1, t2) => {
                match t1.eval1(ctx.clone()) {
                    (t, true) => changed(Arr(Box::new(t), t2)),
                    (t1, false) => {
                        let arr = |t| Arr(Box::new(t1), Box::new(t));
                        match t2.eval1(ctx) {
                            (t, true) => changed(arr(t)),
                            (t, false) => unchanged(arr(t)),
                        }
                    }
                }
            }
        }
    }

    fn map<F>(self, onvar: &F, c: usize) -> Type
    where
        F: Fn(usize, usize, usize) -> Type,
    {
        use self::Type::*;
        macro_rules! map {
            ($t:expr, $c:expr) => {
                Box::new($t.map(onvar, $c))
            }
        }
        match self {
            Var(x, n) => onvar(c, x, n),
            Abs(i, k, t) => Abs(i, k, map!(t, c + 1)),
            App(t1, t2) => App(map!(t1, c), map!(t2, c)),
            Arr(t1, t2) => Arr(map!(t1, c), map!(t2, c)),
        }
    }

    fn shift_above(self, d: isize, c: usize) -> Type {
        use self::Type::*;
        let f = |c, x, n| {
            let nn = (n as isize + d) as usize;
            if x >= c {
                let xx = x as isize + d;
                Var(xx as usize, nn)
            } else {
                Var(x, nn)
            }
        };
        self.map(&f, c)
    }

    fn shift(self, d: isize) -> Type {
        self.shift_above(d, 0)
    }

    fn subst(self, j: usize, t: &Type) -> Type {
        let f = |j, x, n| if x == j {
            t.clone().shift(j as isize)
        } else {
            Type::Var(x, n)
        };
        self.map(&f, j)
    }

    fn subst_top(self, t: Type) -> Type {
        self.subst(0, &t.shift(1)).shift(-1)
    }
}

impl Term {
    fn type_of(&self, ctx: Context) -> Result<Type, TypeError> {
        use self::Term::*;
        use self::TypeError::*;
        use self::Kind;
        match *self {
            Var(x, n) => ctx.get_type(x).ok_or_else(|| Unbound(x, ctx)),
            Abs(ref i, ref ty1, ref t) => {
                match ty1.kind_of(ctx.clone())? {
                    Kind::Star => (),
                    k => return Err(NotStar(k)),
                }
                let ctx1 = ctx.clone().add(i.clone(), Binding::Term(ty1.clone()));
                let ty2 = t.type_of(ctx1)?;
                let x = Type::Arr(Box::new(ty1.clone()), Box::new(ty2));
                Ok(x)
            }
            App(ref t1, ref t2) => {
                let ty2 = t2.type_of(ctx.clone())?;
                match t1.type_of(ctx.clone())?.eval_to_arr(ctx.clone()) {
                    Type::Arr(ty11, ty12) => {
                        let ty11 = ty11.eval(ctx.clone());
                        let ty2 = ty2.eval(ctx);
                        if ty11 == ty2 {
                            Ok(*ty12)
                        } else {
                            Err(Unexpected(ty2, ty11))
                        }
                    }
                    ty1 => Err(NotArr(ty1)),
                }
            }
        }
    }
}

impl Context {
    fn get(&self, x: usize) -> Option<Binding> {
        self.0.get(x).map(|t| t.1.clone())
    }

    fn get_kind(&self, x: usize) -> Option<Kind> {
        self.get(x).and_then(|y| match y {
            Binding::Type(k) => Some(k),
            _ => None,
        })
    }

    fn get_type(&self, x: usize) -> Option<Type> {
        self.get(x).and_then(|y| match y {
            Binding::Term(t) => Some(t),
            _ => None,
        })
    }

    fn add(mut self, i: String, b: Binding) -> Context {
        self.0.push((i, b));
        self
    }
}
