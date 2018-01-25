//! A type system which is Rank-2 fragment of System F.

use {Shift, Subst};

#[derive(Clone)]
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

    fn rotate(self, n: usize) -> Self {
        self.shift(1).subst(n, &Term::Var(0, n))
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
    fn subst(self, j: usize, t: &Self) -> Self {
        let f = |j, x, n| if x == j {
            t.clone().shift(j as isize)
        } else {
            Term::Var(x, n)
        };
        self.map(&f, j)
    }
}

/// A term in theta-normal form.
pub struct Theta(usize, Vec<Term>);

impl From<Term> for Theta {
    /// Performs theta-reduction of a term.
    fn from(t: Term) -> Theta {
        Theta::from_term(t, 0)
    }
}

impl Theta {
    fn from_right(t: Term, l: usize) -> Vec<Term> {
        use self::Term::*;
        match t {
            Var(..) => vec![t],
            Abs(t) => {
                let mut v = Theta::from_right(*t, l + 1);
                let mut i = v.len() + 1;
                v.into_iter()
                    .map(|t| {
                        i -= 1;
                        t.rotate(i)
                    })
                    .collect()
            }
            App(t, t1) => {
                let mut v1 = Theta::from_right(*t, l);
                let mut v2 = Theta::from_right(*t1, l);
                Theta::app_right(v1, v2)
            }
        }
    }

    fn app_right(v1: Vec<Term>, v2: Vec<Term>) -> Vec<Term> {
        let mut v1 = v1.into_iter();
        let mut v2 = v2.into_iter();
        v1.by_ref().map(
            |t| t.shift_above(1, (v2.len() - 1) as isize),
        );
        if let Some(t2) = v2.next() {
            let t2 = t2.shift_above(1, (v1.len() - 1) as isize);
            if let Some(t1) = v1.next() {
                let mut v1: Vec<_> = vec![app!(t1, t2)].into_iter().chain(v1).collect();
                v1.extend(v2);
                v1
            } else {
                panic!("empty term");
            }
        } else {
            panic!("empty term");
        }
    }

    fn from_term(t: Term, l: usize) -> Theta {
        use self::Term::*;
        match t {
            Var(..) => Theta(0, vec![t]),
            Abs(t) => {
                let Theta(n, v) = Theta::from_term(*t, l + 1);
                Theta(n + 1, v)
            }
            App(t, t1) => {
                let Theta(n, v) = Theta::from_term(*t, l);
                let v1 = Theta::app_right(v, Theta::from_right(*t1, l));
                Theta(n, v1)
            }
        }
    }
}

/// Acyclic Semi-Unification Problem.
pub mod asup {
    use rank2_system_f::lambda2_restricted::lambda2::Rank0;
    use rank2_system_f::lambda2_restricted::Restricted1;
    use rank2_system_f::lambda2_restricted::Restricted2F;
    use rank2_system_f::{Term, Theta};

    #[derive(Clone, PartialEq)]
    pub enum Var {
        W(usize, usize),
        X(usize, usize),
        Y(usize, usize),
        Z(usize),
    }

    #[derive(Clone, PartialEq)]
    pub enum Type {
        Var(Var),
        Term(usize),
        Arr(Box<Type>, Box<Type>),
    }

    pub struct Instance(pub Vec<(Type, Type)>);

    pub struct Constructor {
        n: usize,
        /// 1 plus the maximum index of free variables.
        /// Under the assumption that the indices are continuous, It's the number of free
        /// variables.
        w: usize,
    }

    struct Context {
        ws: usize,
        xs: usize,
        ys: usize,
    }

    #[derive(Clone, PartialEq)]
    enum Direction {
        Left,
        Right,
    }

    fn reduce1(t1: &Box<Type>, t2: &Box<Type>, mut v: &[Direction]) -> Option<(Type, Type)> {
        use self::Direction::*;
        if let Some(l) = t2.left() {
            let mut v = v.to_vec();
            v.push(Left);
            if let Some((t1, t2)) = reduce1(t1, l, &v) {
                return Some((t1, t2));
            }
        }
        if let Some(r) = t2.right() {
            let mut v = v.to_vec();
            v.push(Right);
            if let Some((t1, t2)) = reduce1(t1, r, &v) {
                return Some((t1, t2));
            }
        }
        if let Some(t) = Type::redo(t1, v) {
            match **t {
                Type::Arr(..) => {
                    return Some((*t2.clone(), *t.clone()));
                }
                _ => {
                    return None;
                }
            }
        }
        None
    }

    fn reduce2(t1: &Box<Type>, t2: &Box<Type>, mut v: &[Direction]) -> Option<(Type, Type)> {
        let paths = self.variable_paths(t1, v);
        for p1 in paths {
            for p2 in paths {
                if p1 == p2 {
                    continue;
                }
                if let Some(t11) = Type::redo(t1, p1) {
                    if let Some(t12) = Type::redo(t1, p2) {
                        if t11 != t12 {
                            continue;
                        }
                        if let Some(t21) = Type::redo(t2, p1) {
                            if let Some(t21) = Type::redo(t2, p2) {
                                if let Some(p) = var_and_type(t21, t22, &[]) {
                                    return Some(p);
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    fn var_and_type(t1: &Box<Type>, t2: &Box<Type>, mut v: &[Direction]) -> Option<(Type, Type)> {
        use self::Direction::*;
        if let Some(l) = t1.left() {
            let mut v = v.to_vec();
            v.push(Left);
            if let Some(p) = var_and_type(l, t2, &v) {
                return Some(p);
            }
        }
        if let Some(r) = t1.right() {
            let mut v = v.to_vec();
            v.push(Right);
            if let Some(p) = var_and_type(r, t2, &v) {
                return Some(p);
            }
        }
        if let Some(t2) = Type::redo(t2, v) {
            if t2 == t1 {
                return None;
            }
            if t2.contains(t1) {
                return None;
            }
            return Some((*t1.clone(), *t2.clone()));
        }
        None
    }

    fn variable_paths(t1: &Box<Type>, mut v: &[Direction]) -> Vec<Vec<Direction>> {
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
        fn arr(t1: Type, t2: Type) -> Type {
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

        fn redo<'a>(s: &'a Box<Self>, v: &[Direction]) -> Option<&'a Box<Type>> {
            let mut t = s;
            for d in v {
                match t.left_or_right(d) {
                    Some(x) => t = x,
                    None => return None,
                }
            }
            Some(t)
        }

        fn contains(&self, t: &Self) -> bool {
            use self::Type::*;
            match *self {
                Arr(a, b) => {
                    a.contains(t) || b.contains(t)
                }
                _ => {
                    self == t
                }
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
                ws: 0,
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

        /// Constructs for a lambda term an ASUP instance.
        pub fn construct(&mut self, t: Theta) -> Instance {
            use rank2_system_f::Term;
            use self::Var::*;
            let Theta(m, v) = t;
            let mut ctx = Context::new(m);
            let l = v.len();
            let mut inst = Instance::new();
            for (i, t) in v.into_iter().rev().enumerate() {
                let (ty, mut inst1) = self.term(t, i, &ctx, &[]);
                if i < l - 1 {
                    ctx.ys += 1;
                    inst1.add(self.unify(Type::Var(Var::Y(i + 1, i)), ty));
                }
                inst = inst.append(inst1);
            }
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
            for j in 0..ctx.ys {
                for i in j..ctx.ys {
                    inst.add_var(Y(i + 1, j), Y(i + 2, j))
                }
            }
            inst
        }

        fn record_fv(&mut self, n: usize) {
            if self.w < n + 1 {
                self.w = n + 1
            }
        }

        fn term(&mut self, t: Term, i: usize, ctx: &Context, mut l: &[usize]) -> (Type, Instance) {
            use self::Term::*;
            use self::Var::*;
            match t {
                Var(x, _) => {
                    let var = ctx.get(x, i, l);
                    if let W(_, n) = var {
                        self.record_fv(n)
                    }
                    let v = self.fresh();
                    (v.clone(), Instance(vec![(Type::Var(var), v)]))
                }
                App(t, t1) => {
                    let (ty1, inst1) = self.term(*t, i, ctx, l);
                    let (ty2, inst2) = self.term(*t1, i, ctx, l);
                    let v = self.fresh();
                    (
                        v.clone(),
                        Instance(vec![(ty1, Type::arr(ty2, v))])
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
                        Instance(vec![(Type::arr(Type::Var(Z(z)), ty), v)]).append(inst),
                    )
                }
            }
        }
    }
}

pub mod lambda2_restricted {
    use self::lambda2::*;

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

        fn subst(self, j: usize, t: Term) -> Self {
            use self::Term::*;
            let f = |j, x, n| if x == j {
                t.clone().shift(j as isize)
            } else {
                Var(x, n)
            };
            self.map(&f, j)
        }

        pub fn subst_top(self, t: Term) -> Self {
            self.subst(0, t)
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

    pub mod lambda2 {
        pub use Shift;

        #[derive(Clone)]
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
}
