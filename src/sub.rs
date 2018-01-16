//! Lambda calculus with subtypes.
#![warn(missing_docs)]

#[derive(Clone, Debug, PartialEq)]
enum Type {
    Arr(Box<Type>, Box<Type>),
    Top,
}

#[derive(Clone, Debug, PartialEq)]
struct Context(Vec<(String, Binding)>);

#[derive(Clone, Debug, PartialEq)]
enum Binding {
    Term(Type),
}

#[derive(Clone, Debug, PartialEq)]
enum Term {
    Var(usize, usize),
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
}

enum TypeError {
}

impl Type {
    fn subtype_of(&self, ty: &Type) -> bool {
        use self::Type::*;
        match *ty {
            Top => true,
            Arr(ref ty1, ref ty2) => {
                match *ty {
                    Arr(ref ty3, ref ty4) => ty1.subtype_of(ty3) && ty4.subtype_of(ty2),
                    _ => false,
                }
            }
        }
    }
}
