#![cfg(nightly)]
#![feature(box_patterns)]
#![allow(unused)]

use std::collections::HashMap;
use std::collections::HashSet;

use std::fmt;

use std::borrow::Borrow;

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

#[derive(Debug, PartialEq, Clone)]
enum Type {
    Var(String),
    Int,
    Bool,
    Fun(Box<Type>, Box<Type>),
    List(Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Type::Int => write!(f, "Int"),
            Type::Bool => write!(f, "Bool"),
            Type::Var(ref s) => write!(f, "{}", s),
            Type::Fun(ref e1 @ box Type::Fun(..), ref e2) => write!(f, "({}) -> {}", e1, e2),
            Type::Fun(ref e1, ref e2) => write!(f, "{} -> {}", e1, e2),
            Type::List(ref e) => write!(f, "[{}]", e),
        }
    }
}

impl Type {
    fn var(s: &str) -> Type {
        Type::Var(String::from(s))
    }
}

impl Types for Type {
    fn ftv(&self) -> HashSet<String> {
        match self {
            &Type::Var(ref n) => {
                let mut s = HashSet::new();
                s.insert(n.clone());
                s
            }
            &Type::Int | &Type::Bool => HashSet::new(),
            &Type::Fun(box ref t1, box ref t2) => {
                t1.ftv().union(&t2.ftv()).map(|x| x.clone()).collect()
            }
            &Type::List(ref t) => t.ftv(),
        }
    }

    fn apply(&self, s: &Subst) -> Box<Type> {
        match self {
            &Type::Var(ref n) => Box::new(s.get(n).map(|t| t.clone()).unwrap_or(Type::var(n))),
            &Type::Fun(box ref t1, box ref t2) => Box::new(Type::Fun(t1.apply(s), t2.apply(s))),
            &Type::List(ref t) => Box::new(Type::List(t.apply(s))),
            t => Box::new(t.clone()),
        }
    }
}

#[derive(Debug)]
enum Expr {
    Var(String),
    Int(isize),
    Bool(bool),
    App(Box<Expr>, Box<Expr>),
    Abs(String, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    List(Box<Expr>, Box<Expr>),
    Nil,
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expr::Int(n) => write!(f, "{}", n),
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::Var(ref s) => write!(f, "{}", s),
            Expr::Let(ref name, ref e1, ref e2) => write!(f, "let {} = {} in {}", name, e1, e2),
            Expr::If(ref cond, ref e1, ref e2) => write!(f, "if {} then {} else {}", cond, e1, e2),
            Expr::Abs(ref name, ref e) => write!(f, "\\{} -> {}", name, e),
            Expr::App(ref e1, ref e2) => write!(f, "{} {}", e1, e2),
            Expr::List(ref head, ref tail) => write!(f, "{} : {}", head, tail),
            Expr::Nil => write!(f, "nil"),
        }
    }
}

type Subst = HashMap<String, Type>;

fn compose_subst(s1: &Subst, s2: &Subst) -> Subst {
    let mut m: Subst = s2
        .iter()
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

macro_rules! compose {
    ( $x:expr ) => ( $x );
    ( $first:expr, $( $x:expr ),+ ) => {
        compose_subst($first, &compose!( $( $x ),+ ))
    };
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

#[derive(Debug, PartialEq, Clone)]
struct TypeEnv(HashMap<String, Scheme>);

impl TypeEnv {
    fn remove(&mut self, var: &str) {
        self.0.remove(var);
    }

    fn generalize(&self, t: Type) -> Scheme {
        let vars = t.ftv().difference(&self.ftv()).map(|x| x.clone()).collect();
        Scheme {
            vars,
            t: Box::new(t),
        }
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

struct TI {
    supply: usize,
}

impl TI {
    fn new() -> TI {
        TI { supply: 0 }
    }

    fn new_type_var(&mut self, s: &str) -> Type {
        let n = self.supply;
        self.supply += 1;
        Type::Var(format!("{}{}", s, n))
    }

    fn instantiate(&mut self, s: &Scheme) -> Type {
        let nvars = s.vars.iter().map(|_| self.new_type_var("a"));
        let mut m = HashMap::new();
        for (k, v) in s.vars.iter().zip(nvars) {
            m.insert(k.clone(), v);
        }
        let box t = s.t.apply(&m);
        t
    }

    fn var_bind(&self, u: &str, t: Type) -> Subst {
        if t == Type::var(u) {
            return HashMap::new();
        }
        if !t.ftv().contains(u) {
            return HashMap::singleton((String::from(u), t));
        }
        panic!("occur check fails: {} vs. {:?}", u, t);
    }

    fn mgu(&self, t1: Type, t2: Type) -> Subst {
        match (t1, t2) {
            (Type::Fun(box l1, box r1), Type::Fun(box l2, box r2)) => {
                let s1 = self.mgu(l1, l2);
                let box p = r1.apply(&s1);
                let box q = r2.apply(&s1);
                let s2 = self.mgu(p, q);
                compose_subst(&s1, &s2)
            }
            (Type::Var(u), t) | (t, Type::Var(u)) => self.var_bind(&u, t),
            (Type::Int, Type::Int) => HashMap::new(),
            (Type::Bool, Type::Bool) => HashMap::new(),
            (Type::List(t1), Type::List(t2)) => self.mgu(*t1, *t2),
            (t1, t2) => panic!("types do not unify: {:?} vs. {:?}", t1, t2),
        }
    }

    fn ti(&mut self, env: &TypeEnv, expr: &Expr) -> (Subst, Type) {
        match expr {
            &Expr::Var(ref n) => {
                let sigma = env.0.get(n).expect(&format!("unbound variable: {}", n));
                (HashMap::new(), self.instantiate(sigma))
            }
            &Expr::Int(_) => (HashMap::new(), Type::Int),
            &Expr::Bool(_) => (HashMap::new(), Type::Bool),
            &Expr::App(ref e1, ref e2) => {
                let tv = Box::new(self.new_type_var("a"));
                let (s1, t1) = self.ti(env, e1.borrow());
                let (s2, t2) = self.ti(env.apply(&s1).borrow(), &e2);
                let box te = t1.apply(&s2);
                let s3 = self.mgu(te, Type::Fun(Box::new(t2), tv.clone()));
                let box t = tv.apply(&s3);
                (compose!(&s3, &s2, &s1), t)
            }
            &Expr::Abs(ref n, ref e) => {
                let tv = Box::new(self.new_type_var("a"));
                let mut env1 = env.clone();
                env1.0.insert(
                    n.clone(),
                    Scheme {
                        t: tv.clone(),
                        vars: vec![],
                    },
                );
                let (s1, t1) = self.ti(&env1, e);
                let v = tv.apply(&s1);
                (s1, Type::Fun(v, Box::new(t1)))
            }
            &Expr::Let(ref x, ref e1, ref e2) => {
                let (s1, t1) = self.ti(env, e1);
                let mut env1 = env.clone();
                env1.remove(x);
                let t = (env.apply(&s1)).generalize(t1);
                env1.0.insert(x.clone(), t);
                let (s2, t2) = self.ti(env1.apply(&s1).borrow(), e2);
                (compose!(&s1, &s2), t2)
            }
            &Expr::If(ref cond, ref e1, ref e2) => {
                let (s1, t1) = self.ti(env, cond);
                let s2 = self.mgu(*t1.apply(&s1), Type::Bool);
                let (s3, t2) = self.ti(env.apply(&s2).borrow(), e1);
                let (s4, t3) = self.ti(env.apply(&s3).borrow(), e2);
                let s5 = self.mgu(*t2.apply(&s4), *t3.apply(&s4));
                (compose!(&s5, &s4, &s3, &s2, &s1), *t3.apply(&s5))
            }
            &Expr::List(ref head, ref tail) => {
                let (s1, t1) = self.ti(env, head);
                let (s2, t2) = self.ti(env.apply(&s1).borrow(), tail);
                let s3 = self.mgu(Type::List(t1.apply(&s2)), *t2.apply(&s2));
                (compose!(&s3, &s2, &s1), *t2.apply(&s3))
            }
            &Expr::Nil => {
                let tv = self.new_type_var("a");
                (HashMap::new(), tv)
            }
        }
    }

    fn type_inference(&mut self, env: &TypeEnv, expr: &Expr) -> Type {
        let (s, t) = self.ti(env, expr);
        *t.apply(&s)
    }
}

use std::hash::Hash;

trait Singleton {
    type Collection;
    type Item;

    fn singleton(_: Self::Item) -> Self::Collection;
}

impl<Q: Eq + Hash> Singleton for HashSet<Q> {
    type Collection = HashSet<Q>;
    type Item = Q;

    fn singleton(s: Self::Item) -> HashSet<Q> {
        let mut xs = HashSet::new();
        xs.insert(s);
        xs
    }
}

impl<K: Eq + Hash, V> Singleton for HashMap<K, V> {
    type Collection = HashMap<K, V>;
    type Item = (K, V);

    fn singleton((k, v): Self::Item) -> HashMap<K, V> {
        let mut xs = HashMap::new();
        xs.insert(k, v);
        xs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! types {
        ( Fun, $e1:expr, $e2:expr ) => {
            Type::Fun(Box::new($e1), Box::new($e2))
        };
        ( Var, $name:ident ) => {
            Type::Var(String::from(stringify!($name)))
        };
        ( Int ) => {
            Type::Int
        };
        ( Bool ) => {
            Type::Bool
        };
        ( List, $e:expr ) => {
            Type::List(Box::new($e))
        };
    }

    #[test]
    fn test_type_ftv() {
        let t = types!(Var, a);
        let s = HashSet::singleton(String::from("a"));
        assert_eq!(t.ftv(), s);

        let t = Type::Int;
        assert_eq!(t.ftv(), HashSet::new());

        let t = types!(Fun, Type::Int, types!(Var, a));
        let s = HashSet::singleton(String::from("a"));
        assert_eq!(t.ftv(), s);
    }

    #[test]
    fn test_type_apply() {
        let t = types!(Var, a);
        let m = HashMap::singleton((String::from("a"), Type::Int));
        assert_eq!(t.apply(&m), Box::new(Type::Int));

        let t = Type::Int;
        assert_eq!(t.apply(&HashMap::new()), Box::new(Type::Int));

        let t = types!(Fun, types!(Var, c), types!(Var, b));
        let m = HashMap::singleton((String::from("c"), types!(Var, a)));
        assert_eq!(
            t.apply(&m),
            Box::new(types!(Fun, types!(Var, a), types!(Var, b)))
        );
    }

    #[test]
    fn test_scheme_ftv() {
        let s = Scheme {
            vars: vec![String::from("b")],
            t: Box::new(Type::Fun(
                Box::new(Type::var("a")),
                Box::new(Type::var("b")),
            )),
        };
        assert_eq!(s.ftv(), HashSet::singleton(String::from("a")));
    }

    #[test]
    fn test_scheme_apply() {
        let s = Scheme {
            vars: vec![String::from("a")],
            t: Box::new(Type::Fun(
                Box::new(Type::var("a")),
                Box::new(Type::var("c")),
            )),
        };
        let mut m = HashMap::new();
        m.insert(String::from("c"), Type::var("a"));
        m.insert(String::from("a"), Type::var("d"));
        assert_eq!(
            s.apply(&m),
            Box::new(Scheme {
                vars: vec![String::from("a")],
                t: Box::new(Type::Fun(
                    Box::new(Type::var("a")),
                    Box::new(Type::var("a")),
                )),
            })
        );
    }

    #[test]
    fn test_compose_subst() {
        let mut s1 = HashMap::new();
        s1.insert(String::from("a"), Type::var("b"));
        s1.insert(String::from("c"), Type::var("d"));
        let mut s2 = HashMap::new();
        s2.insert(
            String::from("a"),
            Type::Fun(Box::new(Type::var("a")), Box::new(Type::var("b"))),
        );
        let mut want = HashMap::new();
        want.insert(
            String::from("a"),
            Type::Fun(Box::new(Type::var("b")), Box::new(Type::var("b"))),
        );
        want.insert(String::from("c"), Type::var("d"));
        assert_eq!(compose_subst(&s1, &s2), want);
    }

    #[test]
    fn test_type_env_ftv() {
        let s = Scheme {
            vars: vec![String::from("a")],
            t: Box::new(Type::Fun(
                Box::new(Type::var("b")),
                Box::new(Type::var("a")),
            )),
        };
        let m = HashMap::singleton((String::from("b"), s));
        let t = TypeEnv(m);
        assert_eq!(t.ftv(), HashSet::singleton(String::from("b")));
    }

    #[test]
    fn test_type_env_apply() {
        let s = Scheme {
            vars: vec![String::from("a")],
            t: Box::new(Type::Fun(
                Box::new(Type::var("a")),
                Box::new(Type::var("c")),
            )),
        };
        let mut m = HashMap::new();
        m.insert(String::from("c"), Type::var("a"));
        m.insert(String::from("a"), Type::var("d"));

        let t = TypeEnv(HashMap::singleton((String::from("b"), s)));
        assert_eq!(
            t.apply(&m).0,
            HashMap::singleton((
                String::from("b"),
                Scheme {
                    vars: vec![String::from("a")],
                    t: Box::new(Type::Fun(
                        Box::new(Type::var("a")),
                        Box::new(Type::var("a")),
                    )),
                },
            ))
        );
    }

    #[test]
    fn test_type_env_remove() {
        let s = Scheme {
            vars: vec![String::from("a")],
            t: Box::new(Type::Fun(
                Box::new(Type::var("b")),
                Box::new(Type::var("a")),
            )),
        };
        let mut m = HashMap::new();
        m.insert(String::from("b"), s.clone());
        m.insert(String::from("c"), s);
        let mut t = TypeEnv(m);
        t.remove("b");
        assert_eq!(
            t.0,
            HashMap::singleton((
                String::from("c"),
                Scheme {
                    vars: vec![String::from("a")],
                    t: Box::new(Type::Fun(
                        Box::new(Type::var("b")),
                        Box::new(Type::var("a")),
                    )),
                },
            ))
        );
    }

    #[test]
    fn test_ti_new_type_var() {
        let mut ti = TI::new();
        assert_eq!(ti.new_type_var("a"), Type::var("a0"));
        assert_eq!(ti.new_type_var("a"), Type::var("a1"));
        assert_eq!(ti.new_type_var("a"), Type::var("a2"));
    }

    macro_rules! expr {
        ( Let $name:ident
          [ $( $e1:tt )* ]
          [ $( $e2:tt )* ] ) => {
            Expr::Let(
                String::from(stringify!($name)),
                Box::new(expr!($( $e1 )*)),
                Box::new(expr!($( $e2 )*)),
            )
        };
        ( Abs $name:ident [ $( $e:tt )* ] ) => {
            Expr::Abs( String::from(stringify!($name)), Box::new(expr!($( $e )*)) )
        };
        ( App [ $( $e1:tt )* ] [ $($e2:tt)* ] ) => {
            Expr::App( Box::new(expr!($( $e1 )*)), Box::new(expr!($( $e2 )*)) )
        };
        ( Var $name:ident ) => {
            Expr::Var( String::from(stringify!($name)) )
        };
        ( Int $n:expr ) => {
            Expr::Int( $n )
        };
        ( Bool $b:expr ) => {
            Expr::Bool( $b )
        };
        ( If [ $( $cond:tt )* ] [ $( $e1:tt )* ] [ $( $e2:tt )* ] ) => {
            Expr::If(
                Box::new(expr!($( $cond )*)),
                Box::new(expr!($( $e1 )*)),
                Box::new(expr!($( $e2 )*)),
            )
        };
        ( List [ $( $e1:tt )* ] [ $( $e2:tt )* ] ) => {
            Expr::List(
                Box::new(expr!($( $e1 )*)),
                Box::new(expr!($( $e2 )*)),
            )
        };
        ( Nil ) => {
            Expr::Nil
        };
    }

    macro_rules! expr_type {
        ( $e:expr, $t:expr ) => {
            let mut ti = TI::new();
            let m = TypeEnv(HashMap::new());
            assert_eq!(ti.type_inference(&m, &$e), $t);
        };
    }

    #[test]
    fn test_type_inference() {
        expr_type!(expr!(Int 12), types!(Int));

        expr_type!(expr!(Let n [Int 12] [Var n]), types!(Int));

        expr_type!(
            expr!(Let f [Abs x [Var x]] [Var f]),
            types!(Fun, types!(Var, a1), types!(Var, a1))
        );

        expr_type!(
            expr!(Let x [Abs x [Var x]] [App [Var x] [Var x]]),
            types!(Fun, types!(Var, a3), types!(Var, a3))
        );

        expr_type!(
            expr!(
                Let
                length
                [Abs xs [Int 12]]
                [App [Var length] [Var length]]
            ),
            types!(Int)
        );

        expr_type!(expr!(If [Bool true] [Int 12] [Int 61]), types!(Int));
        expr_type!(expr!(If [Bool false] [Int 12] [Int 61]), types!(Int));
        expr_type!(
            expr!(If [Let b [Bool true] [Var b]] [Int 12] [Int 61]),
            types!(Int)
        );
        expr_type!(
            expr!(
                Let
                f
                [
                    If
                    [Bool true]
                    [Abs n [Bool false]]
                    [Abs n [Bool true]]
                ]
                [App [Var f] [Int 61]]
            ),
            types!(Bool)
        );
        expr_type!(
            expr!(If [Bool true] [Abs n [Int 42]] [Abs q [Int 21]]),
            types!(Fun, types!(Var, a1), types!(Int))
        );

        expr_type!(
            expr!(List [Int 12] [List [Int 24] [Nil]]),
            types!(List, types!(Int))
        );
        expr_type!(
            expr!(List [Bool true] [List [Bool false] [Nil]]),
            types!(List, types!(Bool))
        );
        expr_type!(
            expr!(
                Let
                b
                [
                    If
                    [Bool false]
                    [Bool true]
                    [
                        App
                        [
                            Abs
                            n
                            [Bool false]
                        ]
                        [Int 42]
                    ]
                ]
                [List [Bool true] [List [Var b] [Nil]]]
            ),
            types!(List, types!(Bool))
        );
    }

    macro_rules! type_inference_panic {
        ( $name:ident, $e:expr ) => {
            #[test]
            #[should_panic]
            fn $name() {
                let mut ti = TI::new();
                let m = TypeEnv(HashMap::new());
                ti.type_inference(&m, $e);
            }
        };
    }

    type_inference_panic!(
        test_type_inference_fails_app,
        &expr!(Let n [Int 12] [App [Var n] [Int 34]])
    );

    type_inference_panic!(
        test_type_inference_fails_if,
        &expr!(If [Int 10] [Int 12] [Int 34])
    );

    type_inference_panic!(test_type_inference_fails_unbound, &expr!(Var none));

    type_inference_panic!(
        test_type_inference_list_unmatched1,
        &expr!(List [Int 12] [Int 12])
    );

    type_inference_panic!(
        test_type_inference_list_unmatched2,
        &expr!(List [Int 12] [List [Bool true] [Nil]])
    );
}
