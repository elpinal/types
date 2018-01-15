//! System F
#![warn(missing_docs)]

/// Represents a type.
#[derive(Clone)]
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
    fn map<F>(&mut self, onvar: &F, c: isize)
    where
        F: Fn(isize, &isize, &isize),
    {
        match *self {
            Type::Var(ref x, ref n) => onvar(c, x, n),
            Type::Arr(ref mut ty1, ref mut ty2) => {
                ty1.map(onvar, c);
                ty2.map(onvar, c);
            }
            Type::All(_, ref mut ty) => ty.map(onvar, c),
            Type::Some(_, ref mut ty) => ty.map(onvar, c),
        }
    }

    fn shift_above(&mut self, d: isize, c: isize) {
        let f = |c, &x: &isize, &n: &isize| if x >= c {
            x + d;
            n + d;
        } else {
            n + d;
        };
        self.map(&f, c)
    }

    fn shift(&mut self, d: isize) {
        self.shift_above(d, 0)
    }

    fn subst(&mut self, ty: &mut Type, j: isize) {
        let f = |j, &x: &isize, _: &isize| if x == j {
            ty.clone().shift(j)
        };
        self.map(&f, j)
    }

    fn subst_top(&mut self, ty: &mut Type) {
        ty.shift(1);
        self.subst(ty, 0);
        self.shift(-1);
    }
}
