//! The definition of MiniHeapLang

/// Heap locations in HeapLang.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc(usize);

/// HeapLang literals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    Int(i32),
    Bool(bool),
    Unit,
    Loc(Loc),
}

/// Operators in HeapLang.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    MinusUn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Plus,
    Minus,
    Mult,
    Quot,
    Rem,
    And,
    Or,
    Xor,
    ShiftL,
    ShiftR,
    Le,
    Lt,
    Eq,
    Offset,
}

pub type Binder = Option<String>;

/// HeapLang expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Val(Box<Val>),
    Var(String),
    Rec {
        fun_name: Binder,
        arg_name: Binder,
        expr: Box<Expr>,
    },
    App(Box<Expr>, Box<Expr>),
    UnOp(UnOp, Box<Expr>),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
    Pair(Box<Expr>, Box<Expr>),
    Fst(Box<Expr>),
    Snd(Box<Expr>),
    InjL(Box<Expr>),
    InjR(Box<Expr>),
    Case {
        match_expr: Box<Expr>,
        left_name: Binder,
        left_case: Box<Expr>,
        right_name: Binder,
        right_case: Box<Expr>,
    },
    Fork(Box<Expr>),
    AllocN {
        array_len: Box<Expr>,
        initial_val: Box<Expr>,
    },
    Free(Box<Expr>),
    Load(Box<Expr>),
    Store(Box<Expr>, Box<Expr>),
    CmpXchg {
        location: Box<Expr>,
        expected_val: Box<Expr>,
        new_expr_val: Box<Expr>,
    },
    Xchg {
        location: Box<Expr>,
        new_expr_val: Box<Expr>,
    },
    FAA {
        location: Box<Expr>,
        summand: Box<Expr>,
    },
}

/// HeapLang values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Val {
    LitV(Literal),
    RecV {
        fun_name: Binder,
        arg_name: Binder,
        expr: Box<Expr>,
    },
    PairV(Box<Val>, Box<Val>),
    InjLV(Box<Val>),
    InjR(Box<Val>),
}

impl Expr {
    pub fn subst_var(&mut self, var_name: String, new_val: Val) {
        match self {
            Expr::Val(_) => (),
            Expr::Var(v) => {
                if v == &var_name {
                    *self = Expr::Val(Box::new(new_val));
                }
            }
            Expr::Rec {
                fun_name,
                arg_name,
                expr,
            } => {
                if fun_name != &Some(var_name.clone()) && arg_name != &Some(var_name.clone()) {
                    expr.subst_var(var_name, new_val)
                }
            }
            Expr::App(app, arg) => {
                app.subst_var(var_name.clone(), new_val.clone());
                arg.subst_var(var_name, new_val)
            }
            Expr::UnOp(_, arg) => arg.subst_var(var_name, new_val),
            Expr::BinOp(_, arg1, arg2) => {
                arg1.subst_var(var_name.clone(), new_val.clone());
                arg2.subst_var(var_name, new_val)
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                condition.subst_var(var_name.clone(), new_val.clone());
                then_branch.subst_var(var_name.clone(), new_val.clone());
                else_branch.subst_var(var_name, new_val)
            }
            Expr::Pair(fst, snd) => {
                fst.subst_var(var_name.clone(), new_val.clone());
                snd.subst_var(var_name, new_val)
            }
            Expr::Fst(prod) => prod.subst_var(var_name, new_val),
            Expr::Snd(prod) => prod.subst_var(var_name, new_val),
            Expr::InjL(sum) => sum.subst_var(var_name, new_val),
            Expr::InjR(sum) => sum.subst_var(var_name, new_val),
            Expr::Case {
                match_expr,
                left_name,
                left_case,
                right_name,
                right_case,
            } => {
                match_expr.subst_var(var_name.clone(), new_val.clone());
                if left_name != &Some(var_name.clone()) {
                    left_case.subst_var(var_name.clone(), new_val.clone());
                }
                if right_name != &Some(var_name.clone()) {
                    right_case.subst_var(var_name, new_val)
                }
            }
            Expr::Fork(new_thread) => new_thread.subst_var(var_name, new_val),
            Expr::AllocN {
                array_len,
                initial_val,
            } => {
                array_len.subst_var(var_name.clone(), new_val.clone());
                initial_val.subst_var(var_name, new_val)
            }
            Expr::Free(loc) => loc.subst_var(var_name, new_val),
            Expr::Load(loc) => loc.subst_var(var_name, new_val),
            Expr::Store(loc, new_e_val) => {
                loc.subst_var(var_name.clone(), new_val.clone());
                new_e_val.subst_var(var_name, new_val)
            }
            Expr::CmpXchg {
                location,
                expected_val,
                new_expr_val,
            } => {
                location.subst_var(var_name.clone(), new_val.clone());
                expected_val.subst_var(var_name.clone(), new_val.clone());
                new_expr_val.subst_var(var_name, new_val)
            }
            Expr::Xchg {
                location,
                new_expr_val,
            } => {
                location.subst_var(var_name.clone(), new_val.clone());
                new_expr_val.subst_var(var_name, new_val)
            }
            Expr::FAA { location, summand } => {
                location.subst_var(var_name.clone(), new_val.clone());
                summand.subst_var(var_name, new_val)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_subst_var() {
        use self::BinOp::*;
        use self::Val::*;
        use Expr::*;
        use Literal::*;

        let mut expr = If {
            condition: Box::new(BinOp(
                Lt,
                Box::new(Var("x".to_string())),
                Box::new(Val(Box::new(LitV(Int(12))))),
            )),
            then_branch: Box::new(App(
                Box::new(Var("println".to_string())),
                Box::new(Val(Box::new(LitV(Bool(false))))),
            )),
            else_branch: Box::new(App(
                Box::new(Var("y".to_string())),
                Box::new(Var("x".to_string())),
            )),
        };

        let expected = If {
            condition: Box::new(BinOp(
                Lt,
                Box::new(Val(Box::new(LitV(Int(3))))),
                Box::new(Val(Box::new(LitV(Int(12))))),
            )),
            then_branch: Box::new(App(
                Box::new(Var("println".to_string())),
                Box::new(Val(Box::new(LitV(Bool(false))))),
            )),
            else_branch: Box::new(App(
                Box::new(Var("y".to_string())),
                Box::new(Val(Box::new(LitV(Int(3))))),
            )),
        };

        expr.subst_var("x".to_string(), LitV(Int(3)));

        assert_eq!(expr, expected);
    }
}
