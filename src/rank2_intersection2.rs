//! Another approach to rank 2 intersection types.

enum SimpleType {
    Var(String),
    Arr(Box<SimpleType>, Box<SimpleType>),
}

enum Rank1 {
    Simple(SimpleType),
    Intersection(Box<Rank1>, Box<Rank1>),
}

enum Rank2 {
    Simple(SimpleType),
    Arr(Rank1, Box<Rank2>),
}

enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

type Context = Vec<Rank1>;

struct Inference {
    n: usize,
}

impl Inference {
    fn fresh_var(&mut self) -> SimpleType {
        SimpleType::Var(format!("{}", self.n))
    }

    fn type_of(&mut self, t: &Term, ctx: &Context) -> Option<Rank2> {
        use self::Term::*;
        match *t {
            Var(x, _) => {
                Some(Rank2::Simple(self.fresh_var()))
            }
            Abs(t) => {
                let t0 = Rank1::Simple(self.fresh_var());
                Some(Rank2::Arr(t0, self.type_of(&*t, ctx)))
            }
            App(t1, t2) => {
                let t1 = self.type_of(&*t1, ctx);
                let t2 = self.type_of(&*t2, ctx);
                match t1 {
                    Rank2::Arr(t11, t12) => {
                        if t11 == t2 {
                            Some(t12)
                        } else {
                            None
                        }
                    }
                }
            }
        }
    }
}
