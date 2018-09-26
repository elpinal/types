//! Lambda calculus with subtypes.
#![warn(missing_docs)]

#[derive(Clone, Debug, PartialEq)]
enum Type {
    Arr(Box<Type>, Box<Type>),
    Top,
}

#[derive(Clone, Debug, PartialEq)]
struct Context(Vec<(String, Type)>);

#[derive(Clone, Debug, PartialEq)]
enum Term {
    Var(usize, usize),
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

enum TypeError {
    Unbound(usize, Context),
    NotSubtype(Type, Type),
    NotArr(Type),
}

impl Type {
    fn subtype_of(&self, ty: &Type) -> bool {
        use self::Type::*;
        match *ty {
            Top => true,
            Arr(ref ty1, ref ty2) => match *ty {
                Arr(ref ty3, ref ty4) => ty1.subtype_of(ty3) && ty4.subtype_of(ty2),
                _ => false,
            },
        }
    }
}

impl Term {
    fn type_of(&self, ctx: Context) -> Result<Type, TypeError> {
        use self::Term::*;
        use self::Type::*;
        use self::TypeError::*;
        match *self {
            Var(x, _) => ctx.get(x).ok_or_else(|| Unbound(x, ctx)),
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
                        let ty2 = t2.type_of(ctx)?;
                        if ty2.subtype_of(&ty11) {
                            Ok(*ty12)
                        } else {
                            Err(NotSubtype(ty2, *ty11))
                        }
                    }
                    _ => Err(NotArr(ty1)),
                }
            }
        }
    }
}

impl Context {
    fn get(&self, x: usize) -> Option<Type> {
        self.0.get(x).map(|t| t.1.clone())
    }

    fn add(mut self, i: String, ty: Type) -> Context {
        self.0.push((i, ty));
        self
    }
}
