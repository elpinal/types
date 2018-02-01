//! A type system which is Rank-2 fragment of System F.
#![warn(dead_code)]

use self::lambda2_restricted::Restricted1;

use std::iter;

use {Shift, ShiftRef, Subst};

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(usize, usize),
    Abs(Box<Term>),
    App(Box<Term>, Box<Term>),
}

macro_rules! abs {
    ($t1:expr) => {
        Term::Abs(Box::new($t1))
    }
}

macro_rules! app {
    ($t1:expr, $t2:expr) => {
        Term::App(Box::new($t1), Box::new($t2))
    }
}

#[derive(Debug, PartialEq)]
pub struct Type {
    args: Vec<Restricted1>,
    core: asup::Type,
}

impl Term {
    fn act(&self) -> Vec<usize> {
        use self::Term::*;
        match *self {
            Var(..) => Vec::new(),
            Abs(ref t) => {
                let mut v: Vec<usize> = t.act().iter_mut().map(|&mut n| n + 1).collect();
                v.push(0);
                v
            }
            App(ref t1, _) => {
                let mut v = t1.act();
                v.pop();
                v
            }
        }
    }

    fn map<F>(self, onvar: &F, c: usize) -> Self
    where
        F: Fn(usize, usize, usize) -> Self,
    {
        use self::Term::*;
        match self {
            Var(x, n) => onvar(c, x, n),
            Abs(t) => abs!(t.map(onvar, c + 1)),
            App(t1, t2) => app!(t1.map(onvar, c), t2.map(onvar, c)),
        }
    }

    fn map_ref<F>(&mut self, onvar: &F, c: usize)
    where
        F: Fn(usize, usize, usize, &mut Self),
    {
        use self::Term::*;
        match self {
            &mut Var(x, n) => onvar(c, x, n, self),
            &mut Abs(ref mut t) => {
                t.map_ref(onvar, c + 1);
            }
            &mut App(ref mut t1, ref mut t2) => {
                t1.map_ref(onvar, c);
                t2.map_ref(onvar, c);
            }
        }
    }

    /// Swaps the two indices.
    pub fn swap(self, i: usize, j: usize) -> Self {
        use self::Term::*;
        let f = |c, x, n| {
            let i = c + i;
            let j = c + j;
            if x == i {
                Var(j, n)
            } else if x == j {
                Var(i, n)
            } else {
                Var(x, n)
            }
        };
        self.map(&f, 0)
    }

    fn rotate_from(self, c: usize, n: usize, l: usize) -> Self {
        self.shift_above(c, 1)
            .subst(n, &Term::Var(0, l))
            .shift_above(n, -1)
    }

    pub fn infer_type(self) -> Option<(asup::Type, usize, usize)> {
        let tnf = Theta::from(self);
        let Theta(n, _) = tnf;
        let mut c = asup::Constructor::new();
        let (mut ty, inst, ws) = c.construct(tnf);
        let ps = asup::reduce(&c, inst)?;
        for (t1, t2) in ps {
            ty = ty.replace(&t1, &t2);
        }
        Some((ty, n, ws))
    }

    pub fn infer_type_trivial(self) -> Option<Type> {
        let (ty, n, _) = self.infer_type()?;
        let v = iter::repeat(Restricted1::bottom()).take(n).collect();
        Some(Type { args: v, core: ty })
    }

    fn theta_2(&mut self, m: usize) {
        use self::Term::*;
        if m == 0 {
            return;
        }
        let f = |j, x, n, t: &mut Term| if x == j + m {
            *t = Var(0, n);
        } else {
            *t = app!(Var(j + 1, n), Var(j, n));
        };
        self.map_ref(&f, 0);
    }
}

impl ShiftRef for Term {
    fn shift_above_ref(&mut self, c: usize, d: isize) {
        use self::Term::*;
        let var = |x, n| Var(x as usize, n as usize);
        let f = |c: usize, x: usize, n, t: &mut Term| if x >= c {
            *t = var(x as isize + d, n as isize + d);
        } else {
            *t = Var(x, (n as isize + d) as usize);
        };
        self.map_ref(&f, c);
    }
}

impl Subst for Term {
    fn subst(self, j: usize, t: &Self) -> Self {
        let f = |j, x, n| if x == j {
            t.clone().shift(j as isize)
        } else {
            Term::Var(x, n)
        };
        self.map(&f, j)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shift_ref() {
        use self::Term::*;
        let mut t = abs!(Var(0, 1));
        let t0 = abs!(Var(0, 1));
        t.shift_ref(1);
        assert_eq!(t, t0.shift(1));
        assert_eq!(t, abs!(Var(0, 2)));

        let mut t = Var(0, 1);
        let t0 = Var(0, 1);
        t.shift_ref(1);
        assert_eq!(t, t0.shift(1));
        assert_eq!(t, Var(1, 2));
    }

    #[test]
    fn test_rotate_from() {
        use self::Term::*;
        let t = abs!(Var(0, 1));
        assert_eq!(t.clone().rotate_from(0, 1, 1), t);

        let t = abs!(Var(0, 2));
        assert_eq!(t.clone().rotate_from(0, 1, 1), t);
    }

    #[test]
    fn test_rotate_map() {
        use self::Term::*;
        let t = abs!(Var(0, 1));
        assert_eq!(Theta::rotate_map(vec![t.clone()], || 0, 0, 0), vec![t]);

        let t = abs!(Var(0, 2));
        assert_eq!(Theta::rotate_map(vec![t.clone()], || 0, 0, 0), vec![t]);

        let t = abs!(Var(0, 2));
        let mut c = 0;
        assert_eq!(
            Theta::rotate_map(
                vec![t.clone()],
                || {
                    let c0 = c;
                    c += 1;
                    c0
                },
                0,
                0,
            ),
            vec![t]
        );
    }

    #[test]
    fn test_theta_from_left() {
        use self::Term::*;
        let xs = Vec::new();
        let t = abs!(Var(0, 1));
        assert_eq!(Theta::from_left(t, &xs, 0), (
            Theta(0, vec![Var(0, 1)]),
            vec![0],
        ));

        let t = abs!(Var(0, 2));
        assert_eq!(Theta::from_left(t, &xs, 1), (
            Theta(0, vec![Var(0, 2)]),
            vec![0],
        ));
    }

    macro_rules! theta_from {
        ($t: expr, $th: expr) => {
            assert_eq!(Theta::from($t), $th);
        }
    }

    #[test]
    fn test_theta_reduction() {
        use self::Term::*;
        let t = Var(0, 1);
        theta_from!(t.clone(), Theta(0, vec![t]));

        theta_from!(abs!(Var(0, 1)), Theta(1, vec![Var(0, 1)]));

        let t = app!(Var(0, 1), Var(0, 1));
        theta_from!(t.clone(), Theta(0, vec![t]));

        theta_from!(
            abs!(app!(Var(0, 1), Var(0, 1))),
            Theta(1, vec![app!(Var(0, 1), Var(0, 1))])
        );

        theta_from!(
            (app!(abs!(Var(0, 2)), Var(0, 1)), 1),
            Theta(0, vec![Var(0, 1), Var(0, 2)])
        );

        theta_from!(
            app!(abs!(Var(0, 1)), abs!(Var(0, 1))),
            Theta(0, vec![abs!(Var(0, 1)), Var(0, 1)])
        );

        theta_from!(
            app!(abs!(abs!(Var(0, 3))), Var(0, 1)),
            Theta(1, vec![Var(1, 2), Var(1, 3)])
        );

        theta_from!(
            (app!(app!(abs!(abs!(Var(0, 3))), Var(0, 1)), Var(0, 1)), 1),
            Theta(0, vec![Var(0, 1), Var(1, 2), Var(0, 3)])
        );

        theta_from!(
            app!(abs!(Var(0, 1)), abs!(app!(abs!(Var(0, 2)), Var(0, 1)))),
            Theta(
                0,
                vec![abs!(Var(0, 1)), abs!(app!(Var(1, 2), Var(0, 2))), Var(0, 2)],
            )
        );

        theta_from!(
            abs!(app!(
                abs!(Var(0, 2)),
                abs!(app!(abs!(Var(0, 3)), Var(0, 2)))
            )),
            Theta(
                1,
                vec![abs!(Var(0, 2)), abs!(app!(Var(1, 3), Var(0, 3))), Var(0, 3)],
            )
        );

        theta_from!(
            app!(abs!(app!(Var(0, 1), abs!(Var(0, 2)))), abs!(Var(0, 1))),
            Theta(0, vec![abs!(Var(0, 1)), app!(Var(0, 1), abs!(Var(0, 2)))])
        );
    }

    #[test]
    fn test_inference() {
        use self::Term::*;
        use self::asup::Type;
        assert_eq!(Var(0, 1).infer_type(), Some((Type::Term(1), 0, 1)));
        assert_eq!(abs!(Var(0, 1)).infer_type(), Some((Type::Term(1), 1, 0)));
        assert_eq!(
            app!(abs!(Var(0, 1)), abs!(Var(0, 1))).infer_type(),
            Some((Type::arr(Type::Term(10), Type::Term(10)), 0, 0))
        );

        let t = abs!(app!(
            abs!(Var(0, 2)),
            abs!(app!(abs!(Var(0, 3)), Var(0, 2)))
        ));
        assert_eq!(t.infer_type(), Some((Type::Term(20), 1, 0)));

        let t = app!(abs!(abs!(Var(0, 2))), abs!(Var(0, 1)));
        assert_eq!(t.infer_type(), Some((Type::Term(9), 1, 0)));

        let t = app!(abs!(app!(Var(0, 1), abs!(Var(0, 2)))), abs!(Var(0, 1)));
        assert_eq!(
            t.infer_type(),
            Some((Type::arr(Type::Term(11), Type::Term(11)), 0, 0))
        );
    }

    #[test]
    fn test_inference_at_all() {
        use self::Term::*;
        use self::asup::Type;
        use self::Type as T;
        use self::Restricted1;
        assert_eq!(
            Var(0, 1).infer_type_trivial(),
            Some(T {
                args: vec![],
                core: Type::Term(1),
            })
        );

        assert_eq!(
            abs!(Var(0, 1)).infer_type_trivial(),
            Some(T {
                args: vec![Restricted1::bottom()],
                core: Type::Term(1),
            })
        );

        let t = abs!(app!(
            abs!(Var(0, 2)),
            abs!(app!(abs!(Var(0, 3)), Var(0, 2)))
        ));
        assert_eq!(
            t.infer_type_trivial(),
            Some(T {
                args: vec![Restricted1::bottom()],
                core: Type::Term(20),
            })
        );
    }
}

/// A term in theta-normal form.
///
/// `Theta(m, vec![t0, t1, ..., tn])` represents
/// `\\...\(\...(\(\tn)tn-1)t1)t0` where `\t` is a lambda abstraction of `t`
/// on an implicit parameter, and `m` is the number of the outermost abstractions.
#[derive(Debug, PartialEq)]
pub struct Theta(usize, Vec<Term>);

impl From<Term> for Theta {
    /// Performs theta-reduction of a term.
    fn from(t: Term) -> Theta {
        let xs = t.act();
        Theta::from_term(t, &xs, 0)
    }
}

impl From<(Term, usize)> for Theta {
    /// Performs theta-reduction of a term.
    fn from((t, l): (Term, usize)) -> Theta {
        let xs = t.act();
        Theta::from_term(t, &xs, l)
    }
}

impl Theta {
    fn from_term(t: Term, xs: &[usize], l: usize) -> Theta {
        use self::Term::*;
        match t {
            Var(..) => Theta(0, vec![t]),
            Abs(t) => {
                let Theta(n, v) = Theta::from_term(*t, xs, l + 1);
                Theta(n + 1, v)
            }
            App(t1, t2) => {
                let (Theta(n, mut v), mut m) = Theta::from_left(*t1, &xs, l);
                let ys: Vec<usize> = t2.act().into_iter().map(|x| x + l).collect();
                let (mut r, _) = Theta::from_right(*t2, &ys, l);
                r = r.into_iter().map(|t| t.shift(n as isize)).collect();
                Theta::app(&mut v, &mut m, &mut r);
                let v = Theta::app_right(v, r);
                Theta(n, v)
            }
        }
    }

    pub fn from_left(t: Term, xs: &[usize], l: usize) -> (Theta, Vec<usize>) {
        use self::Term::*;
        match t {
            Var(..) => (Theta(0, vec![t]), Vec::new()),
            Abs(t) => {
                let (Theta(n, v), m) = Theta::from_left(*t, xs, l + 1);
                let mut m = m.into_iter().map(|i| i + 1).collect();
                if xs.contains(&l) {
                    (Theta(n + 1, v), m)
                } else {
                    let mut c = 0;
                    let vv = Theta::rotate_map(
                        v,
                        || {
                            let c0 = c;
                            c += 1;
                            c0
                        },
                        n,
                        l + m.len(),
                    );
                    m.push(0);
                    (Theta(n, vv), m)
                }
            }
            App(t1, t2) => {
                let (Theta(n, mut v), mut m) = Theta::from_left(*t1, &xs, l);
                let ys: Vec<usize> = t2.act().into_iter().map(|x| x + l).collect();
                let (mut r, _) = Theta::from_right(*t2, &ys, l);
                r = r.into_iter().map(|t| t.shift(n as isize)).collect();
                Theta::app(&mut v, &mut m, &mut r);
                let v = Theta::app_right(v, r);
                (Theta(n, v), m)
            }
        }
    }

    fn rotate_map<F>(v: Vec<Term>, mut f: F, mut n: usize, mut l: usize) -> Vec<Term>
    where
        F: FnMut() -> usize,
    {
        v.into_iter()
            .map(|t| {
                n += 1;
                l += 1;
                t.rotate_from(f(), n, l)
            })
            .collect()
    }

    fn app(v: &mut Vec<Term>, m: &mut Vec<usize>, r: &mut Vec<Term>) {
        if let Some(i) = m.pop() {
            let mut vv = v.split_off(i);
            r.iter_mut().for_each(|t| t.shift_above_ref(0, i as isize));
            vv.iter_mut().enumerate().for_each(|(x, t)| {
                t.shift_above_ref(1, (x + r.len() - 1) as isize)
            });
            v.append(r);
            v.append(&mut vv);
        }
    }

    fn from_right(t: Term, xs: &[usize], l: usize) -> (Vec<Term>, Vec<usize>) {
        use self::Term::*;
        match t {
            Var(..) => (vec![t], Vec::new()),
            Abs(t) => {
                let (v, m) = Theta::from_right(*t, xs, l + 1);
                let mut m: Vec<usize> = m.into_iter().map(|i| i + 1).collect();
                if xs.contains(&l) {
                    // Theta 2.
                    let v = v.into_iter()
                        .enumerate()
                        .map(|(x, mut t)| {
                            t.theta_2(x);
                            abs!(t)
                        })
                        .collect();
                    (v, m)
                } else {
                    m.push(0);
                    (v, m)
                }
            }
            App(t1, t2) => {
                let (mut v1, mut m1) = Theta::from_right(*t1, xs, l);
                let ys: Vec<usize> = t2.act().into_iter().map(|x| x + l).collect();
                let (mut v2, _) = Theta::from_right(*t2, &ys, l);
                Theta::app(&mut v1, &mut m1, &mut v2);
                (Theta::app_right(v1, v2), Vec::new())
            }
        }
    }

    fn app_right(v1: Vec<Term>, mut v2: Vec<Term>) -> Vec<Term> {
        if v1.is_empty() {
            return v2;
        }
        if v2.is_empty() {
            return v1;
        }
        let l = v2.len() as isize;
        let mut v1: Vec<Term> = v1.into_iter().map(|t| t.shift_above(1, l - 1)).collect();
        let t2 = v2.pop().expect("empty term").shift_above(
            1,
            (v1.len() - 1) as isize,
        );
        let t1 = v1.pop().expect("empty term");
        v2.extend(v1);
        v2.push(app!(t1, t2));
        v2
    }
}

/// Acyclic Semi-Unification Problem.
pub mod asup {
    use rank2_system_f::{Term, Theta};

    use std::collections::HashMap;

    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    pub enum Var {
        W(usize, usize),
        X(usize, usize),
        Y(usize, usize),
        Z(usize),
    }

    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    pub enum Type {
        Var(Var),
        Term(usize),
        Arr(Box<Type>, Box<Type>),
    }

    #[derive(Debug, PartialEq)]
    pub struct Instance(pub Vec<(Type, Type)>);

    pub struct Constructor {
        n: usize,
        /// 1 plus the maximum index of free variables.
        /// Under the assumption that the indices are continuous, It's the number of free
        /// variables.
        w: usize,
    }

    pub struct Context {
        ws: usize,
        xs: usize,
        ys: usize,
    }

    #[derive(Clone, Debug, PartialEq)]
    enum Direction {
        Left,
        Right,
    }

    struct Reducer {
        n: usize,
    }

    #[derive(Debug, PartialEq)]
    enum Error {
        NoSolution,
    }

    pub fn reduce(c: &Constructor, inst: Instance) -> Option<Vec<(Type, Type)>> {
        let mut ps = inst.0;
        let mut ret = Vec::new();
        loop {
            let (mut v, ps1, changed) = reduce0(c, ps)?;
            ret.append(&mut v);
            if !changed {
                return Some(ret);
            }
            ps = ps1;
        }
    }

    fn reduce0(
        c: &Constructor,
        mut ps: Vec<(Type, Type)>,
    ) -> Option<(Vec<(Type, Type)>, Vec<(Type, Type)>, bool)> {
        let mut r = Reducer::from_constructor(c);
        let mut v = Vec::new();
        let mut ps1 = Vec::new();
        let mut changed = false;
        macro_rules! update {
            ($ps:expr, $p0:expr) => {
                $ps.into_iter()
                    .map(|(t1, t2)| {
                        (t1.replace(&$p0.0, &$p0.1), t2.replace(&$p0.0, &$p0.1))
                    })
                    .collect();
            }
        }
        loop {
            let p;
            match ps.pop() {
                None => return Some((v, ps1, changed)),
                Some(x) => p = x,
            }
            let t1 = Box::new(p.0);
            let t2 = Box::new(p.1);
            if let Some(p0) = r.reduce1(&t1, &t2, &[]) {
                ps.push((*t1, *t2));
                ps = update!(ps, p0);
                ps1 = update!(ps1, p0);
                v.push(p0);
                changed = true;
            } else {
                match reduce2(&t1, &t2, &[]) {
                    Err(_) => return None,
                    Ok(p0) => {
                        match p0 {
                            None => {
                                if t1 != t2 {
                                    ps1.push((*t1, *t2));
                                }
                            }
                            Some(p0) => {
                                ps.push((*t1, *t2));
                                ps = update!(ps, p0);
                                ps1 = update!(ps1, p0);
                                v.push(p0);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
    }

    impl Reducer {
        fn from_constructor(c: &Constructor) -> Reducer {
            Reducer { n: c.n }
        }

        /// Returns a pair which is called Redex I, if any.
        fn reduce1(
            &mut self,
            t1: &Box<Type>,
            t2: &Box<Type>,
            v: &[Direction],
        ) -> Option<(Type, Type)> {
            use self::Direction::*;
            if let Some(l) = t2.left() {
                let mut v = v.to_vec();
                v.push(Left);
                if let Some((t1, t2)) = self.reduce1(t1, l, &v) {
                    return Some((t1, t2));
                }
            }
            if let Some(r) = t2.right() {
                let mut v = v.to_vec();
                v.push(Right);
                if let Some((t1, t2)) = self.reduce1(t1, r, &v) {
                    return Some((t1, t2));
                }
            }
            let t1 = Type::redo(t1, v)?;
            match **t1 {
                Type::Arr(..) => {
                    match **t2 {
                        Type::Arr(..) => None,
                        _ => Some((*t2.clone(), self.make_fresh(*t1.clone()))),
                    }
                }
                _ => None,
            }
        }

        fn make_fresh(&mut self, t: Type) -> Type {
            let mut m = HashMap::new();
            self.make_fresh_map(t, &mut m)
        }

        fn make_fresh_map(&mut self, t: Type, m: &mut HashMap<Type, Type>) -> Type {
            use self::Type::*;
            match t {
                Arr(t1, t2) => Type::arr(self.make_fresh_map(*t1, m), self.make_fresh_map(*t2, m)),
                _ => {
                    if let Some(t) = m.get(&t) {
                        return t.clone();
                    }
                    let v = self.fresh();
                    m.insert(t, v.clone());
                    v
                }
            }
        }

        fn fresh(&mut self) -> Type {
            let n = self.n;
            self.n += 1;
            Type::Term(n)
        }
    }

    /// Returns a pair which is called Redex II, if any. Informs the caller of an error if there is
    /// no solution.
    fn reduce2(
        t1: &Box<Type>,
        t2: &Box<Type>,
        v: &[Direction],
    ) -> Result<Option<(Type, Type)>, Error> {
        let paths = variable_paths(t1, v);
        for p1 in &paths {
            for p2 in &paths {
                if let Some((t21, t22)) = f(p1, p2, t1, t2) {
                    if let Some(p) = var_and_type(t21, t22, &[])? {
                        return Ok(Some(p));
                    }
                }
            }
        }
        Ok(None)
    }

    fn f<'a>(
        p1: &[Direction],
        p2: &[Direction],
        t1: &Box<Type>,
        t2: &'a Box<Type>,
    ) -> Option<(&'a Box<Type>, &'a Box<Type>)> {
        if p1 == p2 {
            return None;
        }
        let t11 = Type::redo(t1, &p1)?;
        let t12 = Type::redo(t1, &p2)?;
        if t11 != t12 {
            return None;
        }
        let t21 = Type::redo(t2, &p1)?;
        let t22 = Type::redo(t2, &p2)?;
        Some((t21, t22))
    }

    fn var_and_type(
        t1: &Box<Type>,
        t2: &Box<Type>,
        v: &[Direction],
    ) -> Result<Option<(Type, Type)>, Error> {
        use self::Direction::*;
        if let Some(l) = t1.left() {
            let mut v = v.to_vec();
            v.push(Left);
            if let Some(p) = var_and_type(l, t2, &v)? {
                return Ok(Some(p));
            }
        }
        if let Some(r) = t1.right() {
            let mut v = v.to_vec();
            v.push(Right);
            if let Some(p) = var_and_type(r, t2, &v)? {
                return Ok(Some(p));
            }
        }
        match **t1 {
            Type::Arr(..) => return Ok(None),
            _ => (),
        }
        if let Some(t2) = Type::redo(t2, v) {
            if t1 == t2 {
                return Ok(None);
            }
            if t2.contains(t1) {
                return Err(Error::NoSolution);
            }
            return Ok(Some((*t1.clone(), *t2.clone())));
        }
        Ok(None)
    }

    fn variable_paths(t1: &Box<Type>, v: &[Direction]) -> Vec<Vec<Direction>> {
        use self::Direction::*;
        let mut ret = Vec::new();
        if let Some(l) = t1.left() {
            let mut v = v.to_vec();
            v.push(Left);
            let mut vv = variable_paths(l, &v);
            ret.append(&mut vv);
        }
        if let Some(r) = t1.right() {
            let mut v = v.to_vec();
            v.push(Right);
            let mut vv = variable_paths(r, &v);
            ret.append(&mut vv);
        }
        ret.push(v.to_vec());
        ret
    }

    impl Type {
        pub fn arr(t1: Type, t2: Type) -> Type {
            Type::Arr(Box::new(t1), Box::new(t2))
        }

        fn left(&self) -> Option<&Box<Type>> {
            match *self {
                Type::Arr(ref t, _) => Some(t),
                _ => None,
            }
        }

        fn right(&self) -> Option<&Box<Type>> {
            match *self {
                Type::Arr(_, ref t) => Some(t),
                _ => None,
            }
        }

        fn left_or_right(&self, d: &Direction) -> Option<&Box<Type>> {
            use self::Direction::*;
            match *d {
                Left => self.left(),
                Right => self.right(),
            }
        }

        /// Redo directions on a type.
        fn redo<'a>(s: &'a Box<Self>, v: &[Direction]) -> Option<&'a Box<Type>> {
            let mut t = s;
            for d in v {
                t = t.left_or_right(d)?;
            }
            Some(t)
        }

        fn contains(&self, t: &Self) -> bool {
            use self::Type::*;
            match *self {
                Arr(ref a, ref b) => a.contains(t) || b.contains(t),
                _ => self == t,
            }
        }

        pub fn replace(self, t1: &Type, t2: &Type) -> Self {
            use self::Type::*;
            match self {
                Arr(a, b) => Type::arr(a.replace(t1, t2), b.replace(t1, t2)),
                _ => if self == *t1 { t2.clone() } else { self },
            }
        }
    }

    impl Instance {
        fn new() -> Self {
            Instance(Vec::new())
        }

        fn add(&mut self, p: (Type, Type)) {
            self.0.push(p);
        }

        fn add_var(&mut self, v1: Var, v2: Var) {
            self.add((Type::Var(v1), Type::Var(v2)))
        }

        fn append(mut self, mut i: Instance) -> Instance {
            self.0.append(&mut i.0);
            self
        }
    }

    impl Context {
        fn new(x: usize) -> Self {
            Context {
                ws: 0, // TODO: Perhaps this is not necessary.
                xs: x,
                ys: 0,
            }
        }

        fn get(&self, n: usize, i: usize, zs: &[usize]) -> Var {
            use self::Var::*;
            let l = zs.len();
            if n < l {
                Z(zs[l - 1 - n])
            } else if n - l < self.ys {
                Y(i, n - l)
            } else if n - l - self.ys < self.xs {
                X(i, n - l - self.ys)
            } else {
                W(i, n - l - self.ys - self.xs)
            }
        }
    }

    impl Constructor {
        pub fn new() -> Self {
            Constructor { n: 0, w: 0 }
        }

        fn unify(&mut self, t1: Type, t2: Type) -> (Type, Type) {
            use self::Type::*;
            let a = self.fresh();
            (
                Arr(Box::new(a.clone()), Box::new(a)),
                Arr(Box::new(t1), Box::new(t2)),
            )
        }

        fn fresh_number(&mut self) -> usize {
            let n = self.n;
            self.n += 1;
            n
        }

        fn fresh(&mut self) -> Type {
            Type::Term(self.fresh_number())
        }

        /// Constructs for a lambda term an ASUP instance. Returns also the innermost type and the
        /// number of free variables.
        pub fn construct(&mut self, t: Theta) -> (Type, Instance, usize) {
            use self::Var::*;
            let Theta(m, mut v) = t;
            let mut ctx = Context::new(m);
            let l = v.len();
            let mut inst = Instance::new();
            let innermost = v.pop().expect("empty term");
            let mut prev = self.fresh();
            for (i, t) in v.into_iter().enumerate() {
                let (ty, mut inst1) = self.term(t, i, &ctx, &[]);
                ctx.ys += 1;
                inst1.add(self.unify(Type::Var(Var::Y(i + 1, i)), ty.clone()));
                inst = inst.append(inst1);
                let v = self.fresh();
                inst.add(self.unify(v.clone(), Type::arr(ty, prev)));
                prev = v;
            }
            let (ty, inst1) = self.term(innermost, l - 1, &ctx, &[]);
            inst = inst.append(inst1);
            for j in 0..m {
                for i in 0..ctx.ys {
                    inst.add_var(X(i, j), X(i + 1, j))
                }
            }
            for j in 0..self.w {
                for i in 0..ctx.ys {
                    inst.add_var(W(i, j), W(i + 1, j))
                }
            }
            for j in 1..ctx.ys {
                for i in j..ctx.ys - 1 {
                    inst.add_var(Y(i, j), Y(i + 1, j))
                }
            }
            (ty, inst, self.w)
        }

        fn record_fv(&mut self, n: usize) {
            if self.w < n + 1 {
                self.w = n + 1
            }
        }

        fn term(&mut self, t: Term, i: usize, ctx: &Context, l: &[usize]) -> (Type, Instance) {
            use self::Term::*;
            use self::Var::*;
            match t {
                Var(x, _) => {
                    let var = ctx.get(x, i, l);
                    if let W(_, n) = var {
                        self.record_fv(n)
                    }
                    let v = self.fresh();
                    let p;
                    if let Z(_) = var {
                        p = self.unify(Type::Var(var), v.clone());
                    } else {
                        p = (Type::Var(var), v.clone())
                    }
                    (v, Instance(vec![p]))
                }
                App(t1, t2) => {
                    let (ty1, inst1) = self.term(*t1, i, ctx, l);
                    let (ty2, inst2) = self.term(*t2, i, ctx, l);
                    let v = self.fresh();
                    (
                        v.clone(),
                        Instance(vec![self.unify(ty1, Type::arr(ty2, v))])
                            .append(inst1)
                            .append(inst2),
                    )
                }
                Abs(t) => {
                    let z = self.fresh_number();
                    let mut l = l.to_vec();
                    l.push(z);
                    let (ty, inst) = self.term(*t, i, ctx, &l);
                    l.pop();
                    let v = self.fresh();
                    (
                        v.clone(),
                        Instance(vec![self.unify(Type::arr(Type::Var(Z(z)), ty), v)]).append(inst),
                    )
                }
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        macro_rules! assert_construct {
            ($th:expr, $ty:expr, $inst:expr, $ws:expr) => {
                let mut c = Constructor::new();
                assert_eq!(c.construct($th), ($ty, $inst, $ws));
            }
        }

        #[test]
        fn test_construct() {
            use self::Var::*;
            use self::Type::*;
            use self::Term;
            assert_construct!(
                Theta(0, vec![Term::Var(0, 1)]),
                Term(1),
                Instance(vec![(Var(W(0, 0)), Term(1))]),
                1
            );

            assert_construct!(
                Theta(1, vec![Term::Var(0, 1)]),
                Term(1),
                Instance(vec![(Var(X(0, 0)), Term(1))]),
                0
            );

            assert_construct!(
                Theta(
                    0,
                    vec![
                        abs!(Term::Var(0, 1)),
                        app!(Term::Var(0, 1), abs!(Term::Var(0, 2))),
                    ],
                ),
                Term(15),
                Instance(vec![
                    (
                        Type::arr(Term(5), Term(5)),
                        Type::arr(Type::arr(Var(Z(1)), Term(2)), Term(4))
                    ),
                    (
                        Type::arr(Term(3), Term(3)),
                        Type::arr(Var(Z(1)), Term(2))
                    ),
                    (
                        Type::arr(Term(6), Term(6)),
                        Type::arr(Var(Y(1, 0)), Term(4))
                    ),
                    (
                        Type::arr(Term(8), Term(8)),
                        Type::arr(Term(7), Type::arr(Term(4), Term(0)))
                    ),
                    (
                        Type::arr(Term(16), Term(16)),
                        Type::arr(Term(9), Type::arr(Term(13), Term(15)))
                    ),
                    (Var(Y(1, 0)), Term(9)),
                    (
                        Type::arr(Term(14), Term(14)),
                        Type::arr(Type::arr(Var(Z(10)), Term(11)), Term(13))
                    ),
                    (
                        Type::arr(Term(12), Term(12)),
                        Type::arr(Var(Z(10)), Term(11))
                    ),
                ]),
                0
            );

            assert_construct!(
                Theta(1, vec![Term::Var(0, 1), Term::Var(0, 2)]),
                Term(5),
                Instance(vec![
                    (Var(X(0, 0)), Term(1)),
                    (
                        Type::arr(Term(2), Term(2)),
                        Type::arr(Var(Y(1, 0)), Term(1))
                    ),
                    (
                        Type::arr(Term(4), Term(4)),
                        Type::arr(Term(3), Type::arr(Term(1), Term(0)))
                    ),
                    (Var(Y(1, 0)), Term(5)),
                    (Var(X(0, 0)), Var(X(1, 0))),
                ]),
                0
            );

            assert_construct!(
                Theta(0, vec![abs!(Term::Var(0, 1)), abs!(Term::Var(0, 2))]),
                Term(12),
                Instance(vec![
                    (
                        Type::arr(Term(5), Term(5)),
                        Type::arr(Type::arr(Var(Z(1)), Term(2)), Term(4))
                    ),
                    (
                        Type::arr(Term(3), Term(3)),
                        Type::arr(Var(Z(1)), Term(2))
                    ),
                    (
                        Type::arr(Term(6), Term(6)),
                        Type::arr(Var(Y(1, 0)), Term(4))
                    ),
                    (
                        Type::arr(Term(8), Term(8)),
                        Type::arr(Term(7), Type::arr(Term(4), Term(0)))
                    ),
                    (
                        Type::arr(Term(13), Term(13)),
                        Type::arr(Type::arr(Var(Z(9)), Term(10)), Term(12))
                    ),
                    (
                        Type::arr(Term(11), Term(11)),
                        Type::arr(Var(Z(9)), Term(10))
                    ),
                ]),
                0
            );

            assert_construct!(
                Theta(
                    0,
                    vec![
                        abs!(Term::Var(0, 1)),
                        app!(Term::Var(0, 1), abs!(Term::Var(0, 2))),
                    ],
                ),
                Term(15),
                Instance(vec![
                    (
                        Type::arr(Term(5), Term(5)),
                        Type::arr(Type::arr(Var(Z(1)), Term(2)), Term(4))
                    ),
                    (
                        Type::arr(Term(3), Term(3)),
                        Type::arr(Var(Z(1)), Term(2))
                    ),
                    (
                        Type::arr(Term(6), Term(6)),
                        Type::arr(Var(Y(1, 0)), Term(4))
                    ),
                    (
                        Type::arr(Term(8), Term(8)),
                        Type::arr(Term(7), Type::arr(Term(4), Term(0)))
                    ),
                    (
                        Type::arr(Term(16), Term(16)),
                        Type::arr(Term(9), Type::arr(Term(13), Term(15)))
                    ),
                    (Var(Y(1, 0)), Term(9)),
                    (
                        Type::arr(Term(14), Term(14)),
                        Type::arr(Type::arr(Var(Z(10)), Term(11)), Term(13))
                    ),
                    (
                        Type::arr(Term(12), Term(12)),
                        Type::arr(Var(Z(10)), Term(11))
                    ),
                ]),
                0
            );
        }

        macro_rules! assert_reduce {
            ($v:expr, $t:expr) => {
                let mut c = Constructor::new();
                c.n = 100000; // Take care about conflict of numbers!
                assert_eq!(reduce(&c, Instance($v)), $t);
            }
        }

        #[test]
        fn test_reduce() {
            use self::Type::*;
            use self::Var::*;
            assert_reduce!(vec![(Term(0), Term(0))], Some(vec![]));
            assert_reduce!(vec![(Var(Y(1, 0)), Term(9))], Some(vec![]));
            assert_reduce!(
                vec![(Type::arr(Term(3), Term(3)), Type::arr(Var(Z(1)), Term(2)))],
                Some(vec![(Var(Z(1)), Term(2))])
            );
            assert_reduce!(
                vec![
                    (Var(X(0, 0)), Term(1)),
                    (
                        Type::arr(Term(2), Term(2)),
                        Type::arr(Var(Y(1, 0)), Term(1))
                    ),
                    (
                        Type::arr(Term(4), Term(4)),
                        Type::arr(Term(3), Type::arr(Term(1), Term(0)))
                    ),
                    (Var(Y(1, 0)), Term(5)),
                    (Var(X(0, 0)), Var(X(1, 0))),
                ],
                Some(vec![
                    (Term(3), Type::arr(Term(1), Term(0))),
                    (Var(Y(1, 0)), Term(1)),
                ])
            );

            assert_reduce!(
                vec![
                    (
                        Type::arr(Term(5), Term(5)),
                        Type::arr(Type::arr(Var(Z(1)), Term(2)), Term(4))
                    ),
                    (Type::arr(Term(3), Term(3)), Type::arr(Var(Z(1)), Term(2))),
                    (
                        Type::arr(Term(6), Term(6)),
                        Type::arr(Var(Y(1, 0)), Term(4))
                    ),
                    (
                        Type::arr(Term(8), Term(8)),
                        Type::arr(Term(7), Type::arr(Term(4), Term(0)))
                    ),
                    (
                        Type::arr(Term(13), Term(13)),
                        Type::arr(Type::arr(Var(Z(9)), Term(10)), Term(12))
                    ),
                    (
                        Type::arr(Term(11), Term(11)),
                        Type::arr(Var(Z(9)), Term(10))
                    ),
                ],
                Some(vec![
                    (Var(Z(9)), Term(10)),
                    (Term(12), Type::arr(Term(10), Term(10))),
                    (Term(7), Type::arr(Term(4), Term(0))),
                    (Var(Y(1, 0)), Term(4)),
                    (Var(Z(1)), Term(2)),
                    (Term(4), Type::arr(Term(2), Term(2))),
                ])
            );

            assert_reduce!(
                vec![
                    (
                        Type::arr(Term(13), Term(13)),
                        Type::arr(Type::arr(Var(Z(9)), Term(10)), Term(12))
                    ),
                ],
                Some(vec![(Term(12), Type::arr(Var(Z(9)), Term(10)))])
            );

            assert_reduce!(
                vec![
                    (
                        Type::arr(Term(5), Term(5)),
                        Type::arr(Type::arr(Var(Z(1)), Term(2)), Term(4))
                    ),
                    (Type::arr(Term(3), Term(3)), Type::arr(Var(Z(1)), Term(2))),
                    (
                        Type::arr(Term(6), Term(6)),
                        Type::arr(Var(Y(1, 0)), Term(4))
                    ),
                    (
                        Type::arr(Term(8), Term(8)),
                        Type::arr(Term(7), Type::arr(Term(4), Term(0)))
                    ),
                    (
                        Type::arr(Term(16), Term(16)),
                        Type::arr(Term(9), Type::arr(Term(13), Term(15)))
                    ),
                    (Var(Y(1, 0)), Term(9)),
                    (
                        Type::arr(Term(14), Term(14)),
                        Type::arr(Type::arr(Var(Z(10)), Term(11)), Term(13))
                    ),
                    (
                        Type::arr(Term(12), Term(12)),
                        Type::arr(Var(Z(10)), Term(11))
                    ),
                ],
                Some(vec![
                    (Var(Z(10)), Term(11)),
                    (Term(13), Type::arr(Term(11), Term(11))),
                    (
                        Term(9),
                        Type::arr(Type::arr(Term(11), Term(11)), Term(15))
                    ),
                    (Term(7), Type::arr(Term(4), Term(0))),
                    (Var(Y(1, 0)), Term(4)),
                    (Var(Z(1)), Term(2)),
                    (Term(4), Type::arr(Term(2), Term(2))),
                    (Term(15), Type::arr(Term(11), Term(11))),
                ])
            );
        }

        macro_rules! assert_reduce1 {
            ($t1:expr, $t2:expr, $t3:expr) => {
                let mut r = Reducer { n: 0 };
                assert_eq!(r.reduce1(&Box::new($t1), &Box::new($t2), &[]), $t3);
            }
        }

        #[test]
        fn test_reduce1() {
            use self::Type::*;
            assert_reduce1!(Term(0), Term(0), None);

            assert_reduce1!(
                Type::arr(Term(8), Term(8)),
                Type::arr(Term(7), Type::arr(Term(4), Term(0))),
                None
            );

            assert_reduce1!(
                Type::arr(Term(0), Term(0)),
                Term(1),
                Some((Term(1), Type::arr(Term(0), Term(0))))
            );

            assert_reduce1!(
                Type::arr(Type::arr(Term(0), Term(0)), Term(3)),
                Type::arr(Term(1), Term(2)),
                Some((Term(1), Type::arr(Term(0), Term(0))))
            );

            assert_reduce1!(
                Type::arr(Term(3), Type::arr(Term(0), Term(0))),
                Type::arr(Term(1), Term(2)),
                Some((Term(2), Type::arr(Term(0), Term(0))))
            );

            assert_reduce1!(
                Type::arr(Term(3), Type::arr(Term(0), Term(0))),
                Type::arr(Term(1), Type::arr(Term(4), Term(2))),
                None
            );
        }

        macro_rules! assert_reduce2 {
            ($t1:expr, $t2:expr, $t3:expr) => {
                assert_eq!(reduce2(&Box::new($t1), &Box::new($t2), &[]), $t3);
            }
        }

        #[test]
        fn test_variable_paths() {
            use self::Direction::*;
            use self::Type::*;
            let vv = variable_paths(&Box::new(Type::arr(Term(13), Term(13))), &[]);
            assert_eq!(vv, vec![vec![Left], vec![Right], vec![]]);
        }

        #[test]
        fn test_reduce2() {
            use self::Type::*;
            use self::Var::*;

            assert_reduce2!(Term(0), Term(0), Ok(None));

            assert_reduce2!(
                Type::arr(Term(13), Term(13)),
                Type::arr(Type::arr(Var(Z(9)), Term(10)), Term(12)),
                Ok(Some((Term(12), Type::arr(Var(Z(9)), Term(10)))))
            );

            assert_reduce2!(
                Type::arr(Term(8), Term(8)),
                Type::arr(Term(7), Type::arr(Term(4), Term(0))),
                Ok(Some((Term(7), Type::arr(Term(4), Term(0)))))
            );
        }
    }
}

pub mod lambda2_restricted {
    use Subst;
    use rank2_system_f::lambda2::*;

    #[derive(Clone, Debug, PartialEq)]
    pub enum Restricted1 {
        Forall(usize, Rank0),
    }

    pub enum Restricted2 {
        Var(usize, usize),
        Arr(Restricted1, Box<Restricted2>),
    }

    pub enum Restricted2F {
        Forall(usize, Restricted2),
    }

    #[derive(Clone, Copy)]
    pub enum Index {
        Companion,
        Left,
        Right,
    }

    #[derive(Clone)]
    pub enum Term {
        Var(usize, usize),
        Abs(Index, Box<Term>),
        App(Box<Term>, Box<Term>),
    }

    macro_rules! abs {
        ($t1:expr, $t2:expr) => {
            Abs($t1, Box::new($t2))
        }
    }
    macro_rules! app {
        ($t1:expr, $t2:expr) => {
            App(Box::new($t1), Box::new($t2))
        }
    }

    impl Shift for Term {
        fn shift_above(self, c: usize, d: isize) -> Self {
            use self::Term::*;
            let var = |x, n| Var(x as usize, n as usize);
            let f = |c: usize, x: usize, n| if x >= c {
                var(x as isize + d, n as isize + d)
            } else {
                Var(x, (n as isize + d) as usize)
            };
            self.map(&f, c)
        }
    }

    impl Subst for Term {
        fn subst(self, j: usize, t: &Term) -> Self {
            use self::Term::*;
            let f = |j, x, n| if x == j {
                t.clone().shift(j as isize)
            } else {
                Var(x, n)
            };
            self.map(&f, j)
        }
    }

    impl Term {
        fn map<F>(self, onvar: &F, c: usize) -> Self
        where
            F: Fn(usize, usize, usize) -> Self,
        {
            use self::Term::*;
            match self {
                Var(x, n) => onvar(c, x, n),
                Abs(i, t) => abs!(i, t.map(onvar, c + 1)),
                App(t1, t2) => app!(t1.map(onvar, c), t2.map(onvar, c)),
            }
        }

        /// Swaps the two indices.
        pub fn swap(self, i: usize, j: usize) -> Self {
            use self::Term::*;
            let f = |c, x, n| {
                let i = c + i;
                let j = c + j;
                if x == i {
                    Var(j, n)
                } else if x == j {
                    Var(i, n)
                } else {
                    Var(x, n)
                }
            };
            self.map(&f, 0)
        }
    }

    impl From<super::Term> for Term {
        fn from(t: super::Term) -> Self {
            let v = t.act();
            label(t, v, Index::Left, 0)
        }
    }

    fn label(t: super::Term, v: Vec<usize>, i: Index, x: usize) -> Term {
        use self::Term::*;
        match t {
            super::Term::Var(x, n) => Var(x, n),
            super::Term::Abs(t) => {
                let no_companion = v.contains(&x);
                let tt = Box::new(label(*t, v, i, x + 1));
                if no_companion {
                    Abs(i, tt)
                } else {
                    Abs(Index::Companion, tt)
                }
            }
            super::Term::App(t1, t2) => {
                let v1 = t2.act();
                App(
                    Box::new(label(*t1, v, i, x)),
                    Box::new(label(*t2, v1, Index::Right, x)),
                )
            }
        }
    }

    impl Restricted1 {
        pub fn bottom() -> Self {
            Restricted1::Forall(1, Rank0::Var(0, 1))
        }
    }

    impl Shift for Restricted1 {
        fn shift_above(self, c: usize, d: isize) -> Self {
            use self::Restricted1::*;
            let Forall(n, t) = self;
            Forall(n, t.shift_above(c + n, d))
        }
    }

    impl From<Rank1> for Restricted1 {
        fn from(t: Rank1) -> Self {
            use self::Restricted1::*;
            match t {
                RankN::Var(x, n) => Forall(0, Rank0::Var(x, n)),
                RankN::Arr(t1, t2) => {
                    match Self::from(*t2) {
                        Forall(n, t2) => {
                            Forall(n, Rank0::Arr(Box::new(t1.shift(n as isize)), Box::new(t2)))
                        }
                    }
                }
                RankN::Forall(t) => {
                    match Self::from(*t) {
                        Forall(n, t) => Forall(n + 1, t),
                    }
                }
                // TODO: Is this correct?
                RankN::Sharp(t) => Self::from(*t),
            }
        }
    }

    impl From<Rank2> for Restricted2F {
        fn from(t: Rank2) -> Self {
            use self::Restricted2F::*;
            match t {
                RankN::Var(x, n) => Forall(0, Restricted2::Var(x, n)),
                RankN::Arr(t1, t2) => {
                    let Forall(n, t2) = Self::from(*t2);
                    Forall(
                        n,
                        Restricted2::Arr(Restricted1::from(t1.shift(n as isize)), Box::new(t2)),
                    )
                }
                RankN::Forall(t) => {
                    let Forall(n, t) = Self::from(*t);
                    Forall(n + 1, t)
                }
                // TODO: Is this correct?
                RankN::Sharp(t) => Self::from(*t),
            }
        }
    }
}

pub mod lambda2 {
    pub use Shift;

    #[derive(Clone, Debug, PartialEq)]
    pub enum Rank0 {
        Var(usize, usize),
        Arr(Box<Rank0>, Box<Rank0>),
    }

    pub enum RankN<T> {
        Var(usize, usize),
        Arr(T, Box<RankN<T>>),
        Forall(Box<RankN<T>>),
        Sharp(Box<RankN<T>>),
    }

    pub type Rank1 = RankN<Rank0>;
    pub type Rank2 = RankN<Rank1>;

    impl Shift for Rank0 {
        fn shift_above(self, c: usize, d: isize) -> Self {
            use self::Rank0::*;
            match self {
                Var(x, n) => {
                    let n = n as isize;
                    if x >= c {
                        let x = x as isize;
                        Var((x + d) as usize, (n + d) as usize)
                    } else {
                        Var(x, (n + d) as usize)
                    }
                }
                Arr(t1, t2) => {
                    Arr(
                        Box::new(t1.shift_above(c, d)),
                        Box::new(t2.shift_above(c, d)),
                    )
                }
            }
        }
    }

    impl Shift for Rank1 {
        fn shift_above(self, c: usize, d: isize) -> Self {
            use self::RankN::*;
            match self {
                Var(x, n) => {
                    let n = n as isize;
                    if x >= c {
                        let x = x as isize;
                        Var((x + d) as usize, (n + d) as usize)
                    } else {
                        Var(x, (n + d) as usize)
                    }
                }
                Arr(t1, t2) => Arr(t1.shift_above(c, d), Box::new(t2.shift_above(c, d))),
                Forall(t) => Forall(Box::new(t.shift_above(c + 1, d))),
                Sharp(t) => Sharp(Box::new(t.shift_above(c + 1, d))),
            }
        }
    }
}
