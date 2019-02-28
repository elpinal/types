#![allow(dead_code)]
#![feature(test)]

mod algorithm_w;
pub mod explicit_substitution;
pub mod instantiation;
pub mod label_selective;
pub mod linear;
pub mod omega;
pub mod rank2_intersection;
pub mod rank2_intersection2;
pub mod rank2_system_f;
pub mod sub;
pub mod substitution;
pub mod system_f;
pub mod system_fsub;

pub mod context;

pub trait Shift: Sized {
    fn shift_above(self, c: usize, d: isize) -> Self;

    fn shift(self, d: isize) -> Self {
        self.shift_above(0, d)
    }
}

pub trait ShiftRef: Sized {
    fn shift_above_ref(&mut self, c: usize, d: isize);

    fn shift_ref(&mut self, d: isize) {
        self.shift_above_ref(0, d);
    }
}

impl<T: ShiftRef> Shift for T {
    fn shift_above(mut self, c: usize, d: isize) -> Self {
        self.shift_above_ref(c, d);
        self
    }

    fn shift(mut self, d: isize) -> Self {
        self.shift_ref(d);
        self
    }
}

pub trait Subst: Shift + Clone {
    fn subst(self, j: usize, x: &Self) -> Self;

    fn subst_top(self, x: &Self) -> Self {
        self.subst(0, &x.clone().shift(1)).shift(-1)
    }
}

pub trait SubstRef: ShiftRef + Clone {
    fn subst_ref(&mut self, j: usize, x: &Self);

    fn subst_top_ref(&mut self, x: &Self) {
        self.subst_ref(0, &x.clone().shift(1));
        self.shift_ref(-1)
    }
}

impl<T: SubstRef> Subst for T {
    fn subst(mut self, j: usize, x: &Self) -> Self {
        self.subst_ref(j, x);
        self
    }
}
