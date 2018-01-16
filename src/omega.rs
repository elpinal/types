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
                match t1.type_of(ctx)? {
                    Type::Arr(ty11, ty12) => {
                        if *ty11 == ty2 {
                            Ok(*ty12)
                        } else {
                            Err(Unexpected(ty2, *ty11))
                        }
                    }
                    ty1 => Err(NotArr(ty1)),
                }
            }
        }
    }

    fn eval_to_abs(self, ctx: Context) -> Type {
        use self::Type::*;
        match self {
            Abs(..) => self,
            Var(x, _) => ctx.get_kind(x).ok_or_else(|| Unbound(x, ctx)),
            App(Abs(i, k, t), t2) => t.subst_top(t2),
            Arr(..) => self,
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
