//! System F
#![warn(missing_docs)]

/// Represents a type.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// A type variable. As given `Var(x, n)`, `x` represents de Bruijn index; `n` represents the
    /// size of the context.
    Var(isize, isize),
    /// An arrow type.
    Arr(Box<Type>, Box<Type>),
    /// An universal type. `String` is for the name of the binding type variable.
    All(String, Box<Type>),
    /// An existential type. `String` is for the name of the binding type variable.
    Some(String, Box<Type>),
}

impl Type {
    fn map<F>(self, onvar: &F, c: isize) -> Type
    where
        F: Fn(isize, isize, isize) -> Type,
    {
        match self {
            Type::Var(x, n) => onvar(c, x, n),
            Type::Arr(ty1, ty2) => {
                Type::Arr(Box::new(ty1.map(onvar, c)), Box::new(ty2.map(onvar, c)))
            }
            Type::All(i, ty) => Type::All(i, Box::new(ty.map(onvar, c))),
            Type::Some(i, ty) => Type::Some(i, Box::new(ty.map(onvar, c))),
        }
    }

    fn shift_above(self, d: isize, c: isize) -> Type {
        let f = |c, x, n| if x >= c {
            Type::Var(x + d, n + d)
        } else {
            Type::Var(x, n + d)
        };
        self.map(&f, c)
    }

    fn shift(self, d: isize) -> Type {
        self.shift_above(d, 0)
    }

    fn subst(self, ty: &Type, j: isize) -> Type {
        let f = |j, x, n| if x == j {
            ty.clone().shift(j)
        } else {
            Type::Var(x, n)
        };
        self.map(&f, j)
    }

    fn subst_top(self, ty: Type) -> Type {
        self.subst(&ty.shift(1), 0).shift(-1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! subst_test {
        ( $t1:expr, $t2:expr, $t3:expr ) => {
            assert_eq!($t2.clone().subst_top($t1.clone()), $t3.clone());
        };
    }

    macro_rules! all {
        ( $t1:expr, $t2:expr ) => {
            Type::All($t1.to_string(), Box::new($t2))
        };
    }

    #[test]
    fn test_subst_top() {
        use self::Type::*;

        let t = Var(0, 1);
        subst_test!(t, t, t);
        subst_test!(t, Var(0, 2), t);
        subst_test!(t, Var(1, 2), t);
        subst_test!(t, all!("X", Var(0, 3)), all!("X", Var(0, 1)));
    }
}
