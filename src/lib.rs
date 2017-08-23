#![feature(box_patterns)]

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Clone)]
enum Type {
    Var(String),
    Int,
    Fun(Box<Type>, Box<Type>),
}

impl Types for Type {
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

trait Types {
    fn ftv(&self) -> HashSet<String>;
    fn apply(&self, s: &Subst) -> Box<Self>;
}

impl<T: Types> Types for Vec<T> {
    fn ftv(&self) -> HashSet<String> {
        let mut s = HashSet::new();
        for x in self.iter() {
            s = s.union(&x.ftv()).map(|x| x.clone()).collect();
        }
        s
    }

    fn apply(&self, s: &Subst) -> Box<Vec<T>> {
        Box::new(self.iter().map(|x| x.apply(s)).map(|box x| x).collect())
    }
}

enum Expr {
    Var(String),
    Int(isize),
    App(Box<Expr>, Box<Expr>),
}

type Subst = HashMap<String, Type>;

fn compose_subst(s1: &Subst, s2: &Subst) -> Subst {
    let mut m: Subst = s2.iter()
        .map(|(k, v)| (k, v.apply(s1)))
        .map(|(k, box v)| (k.clone(), v))
        .collect();
    for (k, v) in s1.iter() {
        if !m.contains_key(k) {
            m.insert(k.clone(), v.clone());
        }
    }
    m
}

#[derive(Debug, PartialEq, Clone)]
struct Scheme {
    vars: Vec<String>,
    t: Box<Type>,
}

impl Types for Scheme {
    fn ftv(&self) -> HashSet<String> {
        let mut s = self.t.ftv();
        for v in self.vars.iter() {
            s.remove(v);
        }
        s
    }

    fn apply(&self, s: &Subst) -> Box<Scheme> {
        let mut s = s.clone();
        for v in self.vars.iter() {
            s.remove(v);
        }
        Box::new(Scheme {
            vars: self.vars.clone(),
            t: self.t.apply(&s),
        })
    }
}

#[derive(Debug, PartialEq)]
struct TypeEnv(HashMap<String, Scheme>);

impl TypeEnv {
    fn remove(&mut self, var: &str) {
        self.0.remove(var);
    }
}

impl Types for TypeEnv {
    fn ftv(&self) -> HashSet<String> {
        self.0
            .values()
            .map(|v| v.clone())
            .collect::<Vec<Scheme>>()
            .ftv()
    }

    fn apply(&self, s: &Subst) -> Box<TypeEnv> {
        return Box::new(TypeEnv(
            self.0
                .iter()
                .map(|(k, v)| (k, v.apply(s)))
                .map(|(k, box v)| (k.clone(), v))
                .collect(),
        ));
    }
}

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
    fn test_type_ftv() {
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
    fn test_type_apply() {
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

    #[test]
    fn test_scheme_ftv() {
        let singleton = |v| {
            let mut s = HashSet::new();
            s.insert(v);
            s
        };

        let s = Scheme {
            vars: vec![String::from("b")],
            t: Box::new(Type::Fun(
                Box::new(Type::Var(String::from("a"))),
                Box::new(Type::Var(String::from("b"))),
            )),
        };
        assert_eq!(s.ftv(), singleton(String::from("a")));
    }

    #[test]
    fn test_scheme_apply() {
        let s = Scheme {
            vars: vec![String::from("a")],
            t: Box::new(Type::Fun(
                Box::new(Type::Var(String::from("a"))),
                Box::new(Type::Var(String::from("c"))),
            )),
        };
        let mut m = HashMap::new();
        m.insert(String::from("c"), Type::Var(String::from("a")));
        m.insert(String::from("a"), Type::Var(String::from("d")));
        assert_eq!(
            s.apply(&m),
            Box::new(Scheme {
                vars: vec![String::from("a")],
                t: Box::new(Type::Fun(
                    Box::new(Type::Var(String::from("a"))),
                    Box::new(Type::Var(String::from("a"))),
                )),
            })
        );
    }

    #[test]
    fn test_compose_subst() {
        let mut s1 = HashMap::new();
        s1.insert(String::from("a"), Type::Var(String::from("b")));
        s1.insert(String::from("c"), Type::Var(String::from("d")));
        let mut s2 = HashMap::new();
        s2.insert(
            String::from("a"),
            Type::Fun(
                Box::new(Type::Var(String::from("a"))),
                Box::new(Type::Var(String::from("b"))),
            ),
        );
        let mut want = HashMap::new();
        want.insert(
            String::from("a"),
            Type::Fun(
                Box::new(Type::Var(String::from("b"))),
                Box::new(Type::Var(String::from("b"))),
            ),
        );
        want.insert(String::from("c"), Type::Var(String::from("d")));
        assert_eq!(compose_subst(&s1, &s2), want);
    }

    #[test]
    fn test_type_env_ftv() {
        let singleton = |v| {
            let mut s = HashSet::new();
            s.insert(v);
            s
        };
        let s = Scheme {
            vars: vec![String::from("a")],
            t: Box::new(Type::Fun(
                Box::new(Type::Var(String::from("b"))),
                Box::new(Type::Var(String::from("a"))),
            )),
        };
        let mut m = HashMap::new();
        m.insert(String::from("b"), s);
        let t = TypeEnv(m);
        assert_eq!(t.ftv(), singleton(String::from("b")));
    }

    #[test]
    fn test_type_env_apply() {
        let singleton = |k, v| {
            let mut s = HashMap::new();
            s.insert(k, v);
            s
        };

        let s = Scheme {
            vars: vec![String::from("a")],
            t: Box::new(Type::Fun(
                Box::new(Type::Var(String::from("a"))),
                Box::new(Type::Var(String::from("c"))),
            )),
        };
        let mut m = HashMap::new();
        m.insert(String::from("c"), Type::Var(String::from("a")));
        m.insert(String::from("a"), Type::Var(String::from("d")));

        let mut t = TypeEnv(HashMap::new());
        t.0.insert(String::from("b"), s);
        assert_eq!(
            t.apply(&m).0,
            singleton(
                String::from("b"),
                Scheme {
                    vars: vec![String::from("a")],
                    t: Box::new(Type::Fun(
                        Box::new(Type::Var(String::from("a"))),
                        Box::new(Type::Var(String::from("a"))),
                    )),
                },
            )
        );
    }
}
