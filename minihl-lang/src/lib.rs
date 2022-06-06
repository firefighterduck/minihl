#![feature(box_patterns)]

mod lang_defs;
mod types;

pub use lang_defs::{BinOp, Expr, Literal, UnOp, Val};
pub use types::{Type, TypeDict, TypeError, TypeResult};

fn expect_un_op_type(un_op: &UnOp) -> Type {
    match un_op {
        UnOp::Neg => Type::BoolT,
        UnOp::MinusUn => Type::IntT,
    }
}

fn expect_bin_op_type(bi_op: &BinOp, dict: &mut TypeDict) -> (Type, Type, Type) {
    use Type::*;
    match bi_op {
        BinOp::Plus
        | BinOp::Minus
        | BinOp::Mult
        | BinOp::Quot
        | BinOp::Rem
        | BinOp::ShiftL
        | BinOp::ShiftR => (IntT, IntT, IntT),
        BinOp::And | BinOp::Or | BinOp::Xor => (BoolT, BoolT, BoolT),
        BinOp::Le | BinOp::Lt | BinOp::Eq => (IntT, IntT, BoolT),
        BinOp::Offset => {
            let var = dict.new_var();
            (
                LocationT(Box::new(Free(var))),
                IntT,
                LocationT(Box::new(Free(var))),
            )
        }
    }
}

fn type_check_lit(lit: &Literal, dict: &mut TypeDict) -> TypeResult {
    Ok(match lit {
        Literal::Int(_) => Type::IntT,
        Literal::Bool(_) => Type::BoolT,
        Literal::Unit => Type::UnitT,
        Literal::Loc(_) => {
            let var = dict.new_var();
            Type::LocationT(Box::new(Type::Free(var)))
        }
    })
}

fn type_check_lambda(
    fun_name: &Option<String>,
    arg_name: &Option<String>,
    expr: &Expr,
    dict: &mut TypeDict,
) -> TypeResult {
    let mut old_fun_type = None;
    let mut old_arg_type = None;
    let body_type_var = dict.new_var();
    let arg_type_var = dict.new_var();

    let mut fun_type = Type::FunT(
        Box::new(Type::Free(arg_type_var)),
        Box::new(Type::Free(body_type_var)),
    );

    // Shadow old variables with the same name.
    if let Some(fun_name) = fun_name {
        old_fun_type = dict.insert(fun_name.clone(), fun_type.clone());
    };
    if let Some(arg_name) = arg_name {
        old_arg_type = dict.insert(arg_name.clone(), Type::Free(arg_type_var));
    };

    let body_type = type_check(expr, dict)?;

    // Unshadow the old variables or introduce the new function.
    if let Some(fun_name) = fun_name {
        let typ = old_fun_type.unwrap_or_else(|| fun_type.clone());
        dict.insert(fun_name.clone(), typ);
    };
    if let Some(arg_name) = arg_name {
        let arg_type = dict.get_type(arg_name).unwrap().clone();

        if let Some(old_arg_type) = old_arg_type {
            dict.insert(arg_name.clone(), old_arg_type);
        } else {
            dict.drop_var(arg_name);
        }

        fun_type = Type::FunT(Box::new(arg_type), Box::new(body_type));
    } else {
        fun_type = Type::FunT(Box::new(Type::Free(arg_type_var)), Box::new(body_type));
    }

    Ok(fun_type)
}

fn type_check_val(val: &Val, dict: &mut TypeDict) -> TypeResult {
    match val {
        Val::LitV(lit) => type_check_lit(lit, dict),
        Val::RecV {
            fun_name,
            arg_name,
            expr,
        } => type_check_lambda(fun_name, arg_name, expr, dict),
        Val::PairV(fst, snd) => {
            let fst_type = type_check_val(fst, dict)?;
            let snd_type = type_check_val(snd, dict)?;
            Ok(Type::ProdT(Box::new(fst_type), Box::new(snd_type)))
        }
        Val::InjLV(sum) => {
            if let Type::SumT(left_type, _) = type_check_val(sum, dict)? {
                Ok(*left_type)
            } else {
                Err(TypeError::TypeMismatch)
            }
        }
        Val::InjR(sum) => {
            if let Type::SumT(_, right_type) = type_check_val(sum, dict)? {
                Ok(*right_type)
            } else {
                Err(TypeError::TypeMismatch)
            }
        }
    }
}

fn type_check_sum(
    sum: &Expr,
    dict: &mut TypeDict,
    handler: impl Fn(Type, Type, &mut TypeDict) -> TypeResult,
) -> TypeResult {
    let sum_type = type_check(sum, dict)?;
    let mut expected_sum = Type::SumT(
        Box::new(Type::Free(dict.new_var())),
        Box::new(Type::Free(dict.new_var())),
    );

    let unifier = expected_sum.unify(&sum_type)?;
    dict.fix_from_unifier(&unifier);
    expected_sum.instantiate_from_unifier(&unifier);

    if let Type::SumT(box l_type, box r_type) = expected_sum {
        handler(l_type, r_type, dict)
    } else {
        unreachable!()
    }
}

pub fn type_check(expr: &Expr, dict: &mut TypeDict) -> TypeResult {
    match expr {
        Expr::Val(v) => type_check_val(v, dict),
        Expr::Var(v) => dict.get_type(v).cloned().ok_or(TypeError::VarNotFound),
        Expr::Rec {
            fun_name,
            arg_name,
            expr,
        } => type_check_lambda(fun_name, arg_name, expr, dict),
        Expr::App(f_expr, a_expr) => {
            if let Type::FunT(box arg_type, box mut body_type) = type_check(f_expr, dict)? {
                let arg_type_checked = type_check(a_expr, dict)?;

                let unifier = arg_type_checked.unify(&arg_type)?;
                body_type.instantiate_from_unifier(&unifier);
                dict.fix_from_unifier(&unifier);

                Ok(body_type.clone())
            } else {
                Err(TypeError::TypeMismatch)
            }
        }
        Expr::UnOp(un_op, expr) => {
            let expected_type = expect_un_op_type(un_op);
            let actual_type = type_check(expr, dict)?;
            expected_type
                .unify(&actual_type)
                .map(|unifier| {
                    dict.fix_from_unifier(&unifier);
                    expected_type
                })
                .map_err(From::from)
        }
        Expr::BinOp(bin_op, arg1, arg2) => {
            let (exp_arg1, exp_arg2, res_type) = expect_bin_op_type(bin_op, dict);
            let actual_arg1 = type_check(arg1, dict)?;
            let mut actual_arg2 = type_check(arg2, dict)?;

            let unifier1 = exp_arg1.unify(&actual_arg1)?;
            actual_arg2.instantiate_from_unifier(&unifier1);
            dict.fix_from_unifier(&unifier1);

            let unifier2 = exp_arg2.unify(&actual_arg2)?;
            dict.fix_from_unifier(&unifier2);

            Ok(res_type)
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let cond_type = type_check(condition, dict)?;
            let mut then_type = type_check(then_branch, dict)?;
            let mut else_type = type_check(else_branch, dict)?;

            // Make sure the condition is a boolean
            let unifier1 = cond_type.unify(&Type::BoolT)?;
            then_type.instantiate_from_unifier(&unifier1);
            else_type.instantiate_from_unifier(&unifier1);
            dict.fix_from_unifier(&unifier1);

            // Make sure, both branches have the same type
            let unifier2 = then_type.unify(&else_type)?;
            then_type.instantiate_from_unifier(&unifier2);
            dict.fix_from_unifier(&unifier2);

            Ok(then_type)
        }
        Expr::Pair(fst, snd) => {
            let fst_type = type_check(fst, dict)?;
            let snd_type = type_check(snd, dict)?;
            Ok(Type::ProdT(Box::new(fst_type), Box::new(snd_type)))
        }
        Expr::Fst(prod) => {
            let prod_type = type_check(prod, dict)?;
            let mut expected_prod = Type::ProdT(
                Box::new(Type::Free(dict.new_var())),
                Box::new(Type::Free(dict.new_var())),
            );

            let unifier = expected_prod.unify(&prod_type)?;
            dict.fix_from_unifier(&unifier);
            expected_prod.instantiate_from_unifier(&unifier);

            if let Type::ProdT(box fst, _) = expected_prod {
                Ok(fst)
            } else {
                unreachable!()
            }
        }
        Expr::Snd(prod) => {
            let prod_type = type_check(prod, dict)?;
            let mut expected_prod = Type::ProdT(
                Box::new(Type::Free(dict.new_var())),
                Box::new(Type::Free(dict.new_var())),
            );

            let unifier = expected_prod.unify(&prod_type)?;
            dict.fix_from_unifier(&unifier);
            expected_prod.instantiate_from_unifier(&unifier);

            if let Type::ProdT(_, box snd) = expected_prod {
                Ok(snd)
            } else {
                unreachable!()
            }
        }
        Expr::InjL(sum) => type_check_sum(sum, dict, |left, _, _| Ok(left)),
        Expr::InjR(sum) => type_check_sum(sum, dict, |_, right, _| Ok(right)),
        Expr::Case {
            match_expr,
            left_name,
            left_case,
            right_name,
            right_case,
        } => {
            type_check_sum(match_expr, dict, |l_type, r_type, dict| {
                // Shadow old variables.
                let mut old_left_type = None;
                let mut old_right_type = None;

                if let Some(left_name) = left_name {
                    old_left_type = dict.insert(left_name.clone(), l_type);
                }
                let mut l_case_type = type_check(left_case, dict)?;

                if let Some(right_name) = right_name {
                    old_right_type = dict.insert(right_name.clone(), r_type);
                }

                let r_case_type = type_check(right_case, dict)?;

                //Unshadow old variables in reverse order .
                if let Some(right_name) = right_name {
                    if let Some(old_right_type) = old_right_type {
                        dict.insert(right_name.clone(), old_right_type);
                    } else {
                        dict.drop_var(right_name);
                    }
                }
                if let Some(left_name) = left_name {
                    if let Some(old_left_type) = old_left_type {
                        dict.insert(left_name.clone(), old_left_type);
                    } else {
                        dict.drop_var(left_name);
                    }
                }

                // Make sure, both cases produce the same type.
                let unifier = l_case_type.unify(&r_case_type)?;
                l_case_type.instantiate_from_unifier(&unifier);
                dict.fix_from_unifier(&unifier);

                Ok(l_case_type)
            })
        }
        Expr::Fork(thread) => {
            let thread_type = type_check(thread, dict)?;
            let mut expected_thread_type =
                Type::FunT(Box::new(Type::UnitT), Box::new(Type::Free(dict.new_var())));
            let unifier = expected_thread_type.unify(&thread_type)?;
            expected_thread_type.instantiate_from_unifier(&unifier);
            dict.fix_from_unifier(&unifier);
            Ok(expected_thread_type)
        }
        Expr::AllocN {
            array_len,
            initial_val,
        } => {
            let len_type = type_check(array_len, dict)?;
            let unifier = len_type.unify(&Type::IntT)?;
            dict.fix_from_unifier(&unifier);
            let val_type = type_check(initial_val, dict)?;
            Ok(Type::LocationT(Box::new(val_type)))
        }
        Expr::Free(loc) => {
            let loc_type = type_check(loc, dict)?;
            let var = dict.new_var();
            let unifier = loc_type.unify(&Type::LocationT(Box::new(Type::Free(var))))?;
            dict.fix_from_unifier(&unifier);
            Ok(Type::UnitT)
        }
        Expr::Load(loc) => {
            let mut loc_type = type_check(loc, dict)?;
            let var = dict.new_var();

            let unifier = loc_type.unify(&Type::LocationT(Box::new(Type::Free(var))))?;
            dict.fix_from_unifier(&unifier);
            loc_type.instantiate_from_unifier(&unifier);

            let stored_type = if let Type::LocationT(box stored_type) = loc_type {
                stored_type
            } else {
                unreachable!()
            };
            Ok(stored_type)
        }
        Expr::Store(loc, val) => {
            let stored_type = type_check(val, dict)?;
            let loc_type = type_check(loc, dict)?;
            let unifier = loc_type.unify(&Type::LocationT(Box::new(stored_type)))?;
            dict.fix_from_unifier(&unifier);

            Ok(Type::UnitT)
        }
        Expr::CmpXchg {
            location,
            expected_val,
            new_expr_val,
        } => {
            let mut expected_val_type = type_check(expected_val, dict)?;
            let new_expr_val_type = type_check(new_expr_val, dict)?;
            let unifier1 = expected_val_type.unify(&new_expr_val_type)?;
            expected_val_type.instantiate_from_unifier(&unifier1);
            dict.fix_from_unifier(&unifier1);

            let loc_type = type_check(location, dict)?;
            let unifier2 = loc_type.unify(&Type::LocationT(Box::new(expected_val_type)))?;
            dict.fix_from_unifier(&unifier2);

            Ok(Type::BoolT)
        }
        Expr::Xchg {
            location,
            new_expr_val,
        } => {
            let mut new_expr_val_type = type_check(new_expr_val, dict)?;
            let loc_type = type_check(location, dict)?;
            let unifier = loc_type.unify(&Type::LocationT(Box::new(new_expr_val_type.clone())))?;
            new_expr_val_type.instantiate_from_unifier(&unifier);
            dict.fix_from_unifier(&unifier);

            Ok(new_expr_val_type)
        }
        Expr::FAA { location, summand } => {
            let loc_type = type_check(location, dict)?;
            let unifier = loc_type.unify(&Type::LocationT(Box::new(Type::IntT)))?;
            dict.fix_from_unifier(&unifier);

            let summand_type = type_check(summand, dict)?;
            let unifier = summand_type.unify(&Type::IntT)?;
            dict.fix_from_unifier(&unifier);

            Ok(Type::IntT)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_type_check() -> Result<(), TypeError> {
        use Expr::{App, If, Rec, Var};

        let term = Expr::BinOp(
            BinOp::Lt,
            Box::new(Var("x".to_string())),
            Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(3))))),
        );

        let expected_type = Type::BoolT;
        let mut dict = TypeDict::default();
        let x_var = dict.new_var();
        dict.insert("x".to_string(), Type::Free(x_var));
        assert_eq!(expected_type, type_check(&term, &mut dict)?);

        let term = Rec {
            fun_name: Some("f".to_string()),
            arg_name: Some("x".to_string()),
            expr: Box::new(If {
                condition: Box::new(Expr::BinOp(
                    BinOp::Lt,
                    Box::new(Var("x".to_string())),
                    Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(3))))),
                )),
                then_branch: Box::new(Expr::Val(Box::new(Val::LitV(Literal::Unit)))),
                else_branch: Box::new(App(
                    Box::new(Var("f".to_string())),
                    Box::new(Expr::BinOp(
                        BinOp::Minus,
                        Box::new(Var("x".to_string())),
                        Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(1))))),
                    )),
                )),
            }),
        };
        let expected_type = Type::FunT(Box::new(Type::IntT), Box::new(Type::UnitT));

        let mut dict = TypeDict::default();
        assert_eq!(expected_type, type_check(&term, &mut dict)?);

        Ok(())
    }
}
