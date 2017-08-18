#[derive(Debug, PartialEq)]
enum Type {
    TInt,
    TFun(Box<Type>, Box<Type>),
}

enum Expr {
    EInt,
    EApp,
}

fn ti(e: Expr) -> Option<Type> {
    match e {
        Expr::EInt => Some(Type::TInt),
        Expr::EApp => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ti() {
        assert_eq!(ti(Expr::EInt), Some(Type::TInt));
    }
}
