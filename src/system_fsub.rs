//! System F with subtypes.
#![warn(missing_docs)]

#[derive(Clone, Debug, PartialEq)]
enum Type {
    Var(usize, usize),
    Arr(Box<Type>, Box<Type>),
    Top,
    Forall(String, Box<Type>, Box<Type>),
}

#[derive(Clone, Debug, PartialEq)]
struct Context(Vec<(String, Binding)>);

#[derive(Clone, Debug, PartialEq)]
enum Binding {
    Term(Type),
    Subtype(Type),
}

#[derive(Clone, Debug, PartialEq)]
enum Term {
    Var(usize, usize),
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
    TAbs(String, Type, Box<Term>),
    TApp(Box<Term>, Type),
}

enum TypeError {
}
