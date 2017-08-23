#![feature(box_patterns)]

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Clone)]
enum Type {
    Var(String),
    Int,
    Fun(Box<Type>, Box<Type>),
}

impl Type {
    fn ftv(&self) -> HashSet<String> {
        match self {
            &Type::Var(ref n) => {
                let mut s = HashSet::new();
                s.insert(n.clone());
                s
            }
            &Type::Int => {
                let s = HashSet::new();
                s
            }
            &Type::Fun(box ref t1, box ref t2) => {
                let s: HashSet<_> = t1.ftv().union(&t2.ftv()).map(|x| x.clone()).collect();
                s
            }
        }
    }

    fn apply(&self, s: &Subst) -> Box<Type> {
        match self {
            &Type::Var(ref n) => Box::new(
                s.get(n).map(|t| t.clone()).unwrap_or(Type::Var(n.clone())),
            ),
            &Type::Fun(box ref t1, box ref t2) => Box::new(Type::Fun(t1.apply(s), t2.apply(s))),
            t => Box::new(t.clone()),
        }
    }
}

enum Expr {
    Var(String),
    Int(isize),
    App(Box<Expr>, Box<Expr>),
}

type Subst = HashMap<String, Type>;

struct Env {
    vars: HashMap<String, Type>,
}

impl Env {
    fn new() -> Env {
        Env { vars: HashMap::new() }
    }

    fn def(&mut self, name: &str, e: Expr) {
        let t = self.ti(e).unwrap();
        self.vars.insert(String::from(name), t);
    }

    fn ti(&self, e: Expr) -> Option<Type> {
        match e {
            Expr::Var(s) => {
                match self.vars.get(&s) {
                    Some(t) => Some(t.clone()),
                    None => None,
                }
            }
            Expr::Int(_) => Some(Type::Int),
            Expr::App(box f, box x) => {
                match self.ti(f) {
                    Some(Type::Fun(box t1, box t2)) => {
                        match self.ti(x) {
                            Some(ref t) if t == &t1 => Some(t2),
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ti() {
        let env = Env::new();
        assert_eq!(env.ti(Expr::Int(12)), Some(Type::Int));

        let mut env = Env::new();
        env.vars.insert(
            String::from("f"),
            Type::Fun(Box::new(Type::Int), Box::new(Type::Int)),
        );
        assert_eq!(
            env.ti(Expr::Var(String::from("f"))),
            Some(Type::Fun(Box::new(Type::Int), Box::new(Type::Int)))
        );

        assert_eq!(
            env.ti(Expr::App(
                Box::new(Expr::Var(String::from("f"))),
                Box::new(Expr::Int(12)),
            )),
            Some(Type::Int)
        );
    }

    #[test]
    fn test_ftv() {
        let t = Type::Var(String::from("a"));
        let mut s = HashSet::new();
        s.insert(String::from("a"));
        assert_eq!(t.ftv(), s);

        let t = Type::Int;
        assert_eq!(t.ftv(), HashSet::new());

        let t = Type::Fun(Box::new(Type::Int), Box::new(Type::Var(String::from("a"))));
        let mut s = HashSet::new();
        s.insert(String::from("a"));
        assert_eq!(t.ftv(), s);
    }

    #[test]
    fn test_apply() {
        let t = Type::Var(String::from("a"));
        let mut m = HashMap::new();
        m.insert(String::from("a"), Type::Int);
        assert_eq!(t.apply(&m), Box::new(Type::Int));

        let t = Type::Int;
        assert_eq!(t.apply(&HashMap::new()), Box::new(Type::Int));

        let t = Type::Fun(
            Box::new(Type::Var(String::from("c"))),
            Box::new(Type::Var(String::from("b"))),
        );
        let mut m = HashMap::new();
        m.insert(String::from("c"), Type::Var(String::from("a")));
        assert_eq!(
            t.apply(&m),
            Box::new(Type::Fun(
                Box::new(Type::Var(String::from("a"))),
                Box::new(Type::Var(String::from("b"))),
            ))
        );
    }
}
