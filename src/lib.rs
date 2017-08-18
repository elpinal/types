#[derive(Debug, PartialEq)]
enum Type {
    Int,
    Fun(Box<Type>, Box<Type>),
}

enum Expr {
    Int(isize),
    App(Box<Expr>, Box<Expr>),
}

fn ti(e: Expr) -> Option<Type> {
    match e {
        Expr::Int(_) => Some(Type::Int),
        Expr::App(_, _) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ti() {
        assert_eq!(ti(Expr::Int(12)), Some(Type::Int));
    }
}
