#![feature(box_patterns)]

use std::collections::HashMap;

#[derive(Debug, PartialEq, Clone)]
enum Type {
    Int,
    Fun(Box<Type>, Box<Type>),
}

enum Expr {
    Var(String),
    Int(isize),
    App(Box<Expr>, Box<Expr>),
}

struct Env {
    vars: HashMap<String, Type>,
}

impl Env {
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
        let env = Env { vars: HashMap::new() };
        assert_eq!(env.ti(Expr::Int(12)), Some(Type::Int));

        let mut env = Env { vars: HashMap::new() };
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
}
