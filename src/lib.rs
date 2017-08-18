#[derive(Debug, PartialEq)]
enum Type {
    Int,
    Fun(Box<Type>, Box<Type>),
}

enum Expr {
    Int,
    App,
}

fn ti(e: Expr) -> Option<Type> {
    match e {
        Expr::Int => Some(Type::Int),
        Expr::App => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ti() {
        assert_eq!(ti(Expr::Int), Some(Type::Int));
    }
}
