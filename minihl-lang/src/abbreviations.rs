use crate::{lang_defs::Binder, Expr, Literal, Val};

pub fn lambda_expr(arg_name: Binder, expr: Expr) -> Expr {
    Expr::Rec {
        fun_name: None,
        arg_name,
        expr: Box::new(expr),
    }
}
pub fn lambda_val(arg_name: Binder, expr: Expr) -> Val {
    Val::RecV {
        fun_name: None,
        arg_name,
        expr: Box::new(expr),
    }
}

pub fn let_in(arg: Binder, expr1: Expr, expr2: Expr) -> Expr {
    Expr::App(Box::new(lambda_expr(arg, expr2)), Box::new(expr1))
}

pub fn none_expr() -> Expr {
    Expr::InjL(Box::new(Expr::Val(Box::new(Val::LitV(Literal::Unit)))))
}
pub fn none_val() -> Val {
    Val::InjLV(Box::new(Val::LitV(Literal::Unit)))
}

pub fn some_expr(expr: Expr) -> Expr {
    Expr::InjR(Box::new(expr))
}
pub fn some_val(val: Val) -> Val {
    Val::InjRV(Box::new(val))
}

pub fn cas(loc: Expr, expected: Expr, new: Expr) -> Expr {
    Expr::Snd(Box::new(Expr::CmpXchg {
        location: Box::new(loc),
        expected_val: Box::new(expected),
        new_expr_val: Box::new(new),
    }))
}

pub fn match_expr(
    matcher: Expr,
    left_name: Binder,
    left: Expr,
    right_name: Binder,
    right: Expr,
) -> Expr {
    Expr::Case {
        match_expr: Box::new(matcher),
        left_case: Box::new(lambda_expr(left_name, left)),
        right_case: Box::new(lambda_expr(right_name, right)),
    }
}

pub fn match_opt(matcher: Expr, none: Expr, some_name: Binder, some: Expr) -> Expr {
    match_expr(matcher, None, none, some_name, some)
}

pub fn seq(expr1: Expr, expr2: Expr) -> Expr {
    Expr::App(Box::new(lambda_expr(None, expr2)), Box::new(expr1))
}

pub fn alloc(alloc: Expr) -> Expr {
    Expr::AllocN {
        array_len: Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(1))))),
        initial_val: Box::new(alloc),
    }
}
