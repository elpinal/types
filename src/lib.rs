#![allow(unused)]

mod algorithm_w;
pub mod system_f;
pub mod system_fsub;
pub mod sub;
pub mod omega;
pub mod rank2_intersection;
pub mod rank2_intersection2;
pub mod rank2_system_f;

pub trait Shift: Sized {
    fn shift_above(self, c: usize, d: isize) -> Self;

    fn shift(self, d: isize) -> Self {
        Self::shift_above(self, 0, d)
    }
}

pub trait Subst: Shift {
    fn subst(self, j: usize, x: &Self) -> Self;

    fn subst_top(self, x: &Self) -> Self {
        self.subst(0, &x.shift(1)).shift(-1)
    }
}
