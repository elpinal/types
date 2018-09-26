//! Non-explicit substitution.

/// A type.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// A type variable with the index.
    Var(usize),
    /// An universally-quantified type.
    Forall(Box<Type>),
    /// An arrow type.
    Arr(Box<Type>, Box<Type>),
}

impl Type {
    fn forall(t: Type) -> Type {
        Type::Forall(Box::new(t))
    }

    fn arr(t1: Type, t2: Type) -> Type {
        Type::Arr(Box::new(t1), Box::new(t2))
    }

    fn map<F>(self, onvar: &F, c: usize) -> Type
    where
        F: Fn(usize, usize) -> Type,
    {
        use self::Type::*;
        match self {
            Var(n) => onvar(c, n),
            Forall(t) => Type::forall(t.map(onvar, c + 1)),
            Arr(t1, t2) => Type::arr(t1.map(onvar, c), t2.map(onvar, c)),
        }
    }

    fn shift_above(self, c: usize, d: usize) -> Type {
        use self::Type::*;
        let f = |c0: usize, n: usize| {
            if c0 <= n {
                Var(n + d)
            } else {
                Var(n)
            }
        };
        self.map(&f, c)
    }

    fn shift(self, d: usize) -> Type {
        self.shift_above(0, d)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;

    #[bench]
    fn bench_shift_1(b: &mut Bencher) {
        b.iter(|| Type::Var(0).shift(1).shift(1));
    }

    #[bench]
    fn bench_shift_2(b: &mut Bencher) {
        b.iter(|| Type::Var(0).shift(2));
    }
}
