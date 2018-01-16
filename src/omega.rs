//! Lambda calculus with kinds.
#![warn(missing_docs)]

#[derive(Clone, Debug, PartialEq)]
enum Type {
    Var(usize, usize),
    Abs(String, Box<Type>),
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
}

enum KindError {
    Unbound(usize, Context),
}

impl Type {
    fn kind_of(&self, ctx: Context) -> Result<Type, KindError> {
    }
}

impl Term {
    fn type_of(&self, ctx: Context) -> Result<Type, TypeError> {
        use self::Term::*;
        use self::Type::*;
        use self::TypeError::*;
        match *self {
            Var(x, n) => ctx.get_type(x).ok_or_else(|| Unbound(x, ctx)),
            Abs(ref i, ref ty1, ref t) => {
                let ctx1 = ctx.clone().add(i.clone(), ty1.clone());
                let ty2 = t.type_of(ctx1)?;
                let x = Arr(Box::new(ty1.clone()), Box::new(ty2));
                Ok(x)
            }
            App(ref t1, ref t2) => {
                let ty1 = t1.type_of(ctx.clone())?;
                match ty1 {
                    Arr(ty11, ty12) => {
                        unimplemented!()
                    }
                    _ => Err(NotArr(ty1)),
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
