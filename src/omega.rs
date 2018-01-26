//! Lambda calculus with kinds.

/// A type.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// A type variable with the index and the size of context.
    Var(usize, usize),
    /// A type-level abstraction.
    Abs(String, Kind, Box<Type>),
    /// An application of types.
    App(Box<Type>, Box<Type>),
    /// An arrow type.
    Arr(Box<Type>, Box<Type>),
}

/// A kind.
#[derive(Clone, Debug, PartialEq)]
pub enum Kind {
    /// A kind for a proper type.
    Star,
    /// A kind for a type operator.
    Arr(Box<Kind>, Box<Kind>),
}

/// A context.
#[derive(Clone, Debug, PartialEq)]
pub struct Context(Vec<(String, Binding)>);

/// A binding.
#[derive(Clone, Debug, PartialEq)]
pub enum Binding {
    /// Denotes that a term have a type.
    Term(Type),
    /// Denotes that a type have a kind.
    Type(Kind),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(usize, usize),
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

pub enum TypeError {
    Unbound(usize, Context),
    NotArr(Type),
    Kind(KindError),
    NotStar(Kind),
    Unexpected(Type, Type),
}

/// Represents an error while kinding a type.
#[derive(Clone, Debug, PartialEq)]
pub enum KindError {
    /// A type variable is unbound so that the kind is undefined.
    Unbound(usize, Context),
    /// `Unexpected(k1, k2)` denotes that given `k1`, but want `k2`.
    Unexpected(Kind, Kind),
    /// Expected an arrow kind, but got `k` where `NotArr(k)`.
    NotArr(Kind),
}

impl From<KindError> for TypeError {
    fn from(e: KindError) -> TypeError {
        TypeError::Kind(e)
    }
}

impl Type {
    /// Obtains the kind of a type. Returns an error if the type does not hold its kind.
    pub fn kind_of(&self, ctx: &Context) -> Result<Kind, KindError> {
        use self::Type::*;
        use self::KindError::*;
        match *self {
            Var(x, _) => ctx.get_kind(x).ok_or_else(|| Unbound(x, ctx.clone())),
            Abs(ref i, ref k1, ref t) => {
                let ctx1 = ctx.add(i.clone(), Binding::Type(k1.clone()));
                let k2 = t.kind_of(&ctx1)?;
                let x = Kind::Arr(Box::new(k1.clone()), Box::new(k2));
                Ok(x)
            }
            App(ref t1, ref t2) => {
                let k1 = t1.kind_of(ctx)?;
                match k1 {
                    Kind::Arr(k11, k12) => {
                        let k2 = t2.kind_of(ctx)?;
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
                match t1.kind_of(ctx)? {
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

    fn eval_to_arr(self) -> Type {
        use self::Type::*;
        match self {
            Abs(..) => self,
            Var(..) => self,
            App(t1, t2) => {
                match t1.eval() {
                    Abs(_, _, t) => t.subst_top(*t2),
                    t1 => App(Box::new(t1), t2),
                }
            }
            Arr(..) => self,
        }
    }

    /// Evaluates a type to its normal form.
    pub fn eval(self) -> Type {
        let mut t0 = self;
        loop {
            match t0.eval1() {
                (t, true) => t0 = t,
                (t, false) => return t,
            }
        }
    }

    fn eval1(self) -> (Type, bool) {
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
                match t1.eval1() {
                    (t, true) => changed(app!(t)),
                    (Abs(_, _, t), false) => changed(t.subst_top(*t2)),
                    (t, false) => unchanged(app!(t)), // What should happen?
                }
            }
            Arr(t1, t2) => {
                match t1.eval1() {
                    (t, true) => changed(Arr(Box::new(t), t2)),
                    (t1, false) => {
                        let arr = |t| Arr(Box::new(t1), Box::new(t));
                        match t2.eval1() {
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

    fn eq_without_names(&self, t: &Type) -> bool {
        match *self {
            Type::Abs(_, ref k1, ref t1) => {
                match *t {
                    Type::Abs(_, ref k2, ref t2) => k1 == k2 && t1.eq_without_names(t2),
                    _ => false,
                }
            }
            _ => self == t,
        }
    }
}

impl Term {
    pub fn type_of(&self, ctx: &Context) -> Result<Type, TypeError> {
        use self::Term::*;
        use self::TypeError::*;
        use self::Kind;
        match *self {
            Var(x, _) => ctx.get_type(x).ok_or_else(|| Unbound(x, ctx.clone())),
            Abs(ref i, ref ty1, ref t) => {
                match ty1.kind_of(ctx)? {
                    Kind::Star => (),
                    k => return Err(NotStar(k)),
                }
                let ctx1 = ctx.add(i.clone(), Binding::Term(ty1.clone()));
                let ty2 = t.type_of(&ctx1)?;
                let x = Type::Arr(Box::new(ty1.clone()), Box::new(ty2));
                Ok(x)
            }
            App(ref t1, ref t2) => {
                let ty2 = t2.type_of(ctx)?;
                match t1.type_of(ctx)?.eval_to_arr() {
                    Type::Arr(ty11, ty12) => {
                        let ty11 = ty11.eval();
                        let ty2 = ty2.eval();
                        if ty11.eq_without_names(&ty2) {
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
    /// Gets the binding corresponding to the index `x`.
    pub fn get(&self, x: usize) -> Option<Binding> {
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

    /// Adds a binding.
    pub fn add(&self, i: String, b: Binding) -> Context {
        let mut ctx = self.clone();
        ctx.0.push((i, b));
        ctx
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_kind_of {
        ( $t:expr , $ctx:expr, $k:expr ) => {
            assert_eq!($t.kind_of(&$ctx), $k)
        }
    }

    macro_rules! context {
        ( $($i:expr , $b:expr),* ) => {
            Context(vec![ $( ($i.to_string(), $b) ),* ])
        }
    }

    #[test]
    fn test_kind_of() {
        use self::Type::*;
        let ctx = context!("X", Binding::Type(Kind::Star));
        assert_kind_of!(Var(0, 1), ctx, Ok(Kind::Star));
    }
}
