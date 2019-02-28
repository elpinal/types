use std::collections::HashMap;

#[derive(Clone, PartialEq)]
enum Type {
    Int,
    Var(usize),
    Arr(Box<Type>, Box<Type>),
}

#[derive(Clone)]
struct Scheme {
    qs: usize,
    body: Type,
}

#[derive(Default)]
struct Subst(HashMap<usize, Type>);

impl Subst {
    fn insert(&mut self, n: usize, ty: Type) {
        self.0.insert(n, ty);
    }

    fn get(&self, n: usize) -> Option<&Type> {
        self.0.get(&n)
    }
}

impl Type {
    fn is_general_aux(&self, qs: usize, s: &mut Subst, ty: &Type) -> bool {
        use Type::*;
        match (self, ty) {
            (&Int, &Int) => true,
            (&Int, _) => false,
            (&Arr(ref ty11, ref ty12), &Arr(ref ty21, ref ty22)) => {
                let b1 = ty11.is_general_aux(qs, s, ty21);
                let b2 = ty12.is_general_aux(qs, s, ty22);
                b1 && b2
            }
            (&Arr(..), _) => false,
            (&Var(n), _) => {
                if let Some(ty0) = s.get(n) {
                    ty0.clone().is_general_aux(qs, s, ty)
                } else if qs <= n {
                    self == ty
                } else {
                    s.insert(n, ty.clone());
                    true
                }
            }
        }
    }
}

impl Scheme {
    fn new(qs: usize, body: Type) -> Self {
        Scheme { qs, body }
    }

    fn is_general_aux(&self, s: &mut Subst, ty: &mut Type) -> bool {
        ty.shift(self.qs);
        self.body.is_general_aux(self.qs, s, ty)
    }
}

trait General<RHS> {
    fn is_general(&mut self, other: &mut RHS) -> bool;
}

impl General<Type> for Scheme {
    // Assumes well-kindness.
    fn is_general(&mut self, ty: &mut Type) -> bool {
        self.is_general_aux(&mut Subst::default(), ty)
    }
}

impl General<Scheme> for Scheme {
    fn is_general(&mut self, scheme: &mut Scheme) -> bool {
        self.body.shift(self.qs);
        self.shift(scheme.qs);
        self.body
            .is_general_aux(self.qs, &mut Subst::default(), &self.body)
    }
}

impl From<Type> for Scheme {
    fn from(ty: Type) -> Scheme {
        Scheme { qs: 0, body: ty }
    }
}

trait Shift {
    fn shift_above(&mut self, c: usize, d: usize);

    fn shift(&mut self, d: usize) {
        self.shift_above(0, d);
    }
}

impl Shift for Type {
    fn shift_above(&mut self, c: usize, d: usize) {
        use Type::*;
        match *self {
            Int => (),
            Arr(ref mut ty1, ref mut ty2) => {
                ty1.shift_above(c, d);
                ty2.shift_above(c, d);
            }
            Var(n) => {
                if c <= n {
                    *self = Var(n + d);
                }
            }
        }
    }
}

impl Shift for Scheme {
    fn shift_above(&mut self, c: usize, d: usize) {
        self.body.shift_above(c + self.qs, d);
    }
}

#[cfg(test)]
mod tests {
    #![warn(dead_code)]

    use super::*;

    use quickcheck::empty_shrinker;
    use quickcheck::single_shrinker;
    use quickcheck::Arbitrary;
    use quickcheck::Gen;
    use rand::Rng;

    fn arr(ty1: Type, ty2: Type) -> Type {
        Type::Arr(Box::new(ty1), Box::new(ty2))
    }

    impl Arbitrary for Type {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            use Type::*;
            if g.gen() {
                Int
            } else if g.gen() {
                Var(Arbitrary::arbitrary(g))
            } else {
                arr(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g))
            }
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            use Type::*;
            match *self {
                Int => empty_shrinker(),
                Var(n) => Box::new(single_shrinker(Int).chain(n.shrink().map(Var))),
                Arr(ref ty1, ref ty2) => Box::new(
                    single_shrinker(Int)
                        .chain((ty1.clone(), ty2.clone()).shrink().map(|(x, y)| Arr(x, y))),
                ),
            }
        }
    }

    impl Arbitrary for Scheme {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            Scheme::new(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g))
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(
                (self.qs, self.body.clone())
                    .shrink()
                    .map(|(qs, ty)| Scheme::new(qs, ty)),
            )
        }
    }

    #[test]
    fn test_instance() {
        use Type::*;

        assert!(Scheme::from(Int).is_general(&mut Int));
        assert!(!(Scheme::from(Var(0)).is_general(&mut Int)));
        assert!(!(Scheme::from(Var(1)).is_general(&mut Int)));

        assert!(!(Scheme::from(Var(0)).is_general(&mut arr(Int, Int))));
        assert!(!(Scheme::from(Var(1)).is_general(&mut arr(Int, Int))));

        assert!(!(Scheme::from(Int).is_general(&mut arr(Int, Int))));
        assert!(!(Scheme::from(Int).is_general(&mut Var(0))));

        assert!(Scheme::from(arr(Int, Int)).is_general(&mut arr(Int, Int)));
        assert!(Scheme::new(1, arr(Var(0), Int)).is_general(&mut arr(Int, Int)));
        assert!(Scheme::new(1, arr(Int, Var(0))).is_general(&mut arr(Int, Int)));
        assert!(Scheme::new(2, arr(Var(1), Var(1))).is_general(&mut arr(Int, Int)));

        assert!(Scheme::new(2, arr(Var(0), Var(1))).is_general(&mut arr(Int, Int)));
        assert!(!(Scheme::new(1, arr(Var(0), Var(1))).is_general(&mut arr(Int, Int))));
        assert!(!(Scheme::new(1, arr(Var(0), Var(1))).is_general(&mut arr(Int, Var(1)))));
        assert!(Scheme::new(1, arr(Var(0), Var(1))).is_general(&mut arr(Var(0), Var(0))));

        assert!(!(Scheme::from(arr(Int, Int)).is_general(&mut arr(Var(0), Int))));

        assert!(Scheme::new(2, arr(Var(0), Var(1))).is_general(&mut arr(Var(0), Int)));
        assert!(Scheme::new(2, arr(Var(1), Var(0))).is_general(&mut arr(Var(0), Int)));
        assert!(!(Scheme::new(2, arr(Var(0), Var(0))).is_general(&mut arr(Var(0), Int))));
    }
}
