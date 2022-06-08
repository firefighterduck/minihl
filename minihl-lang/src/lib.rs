#![feature(box_patterns)]
#![feature(let_chains)]

mod lang_defs;
mod types;

pub use lang_defs::{BinOp, Expr, Literal, UnOp, Val};
pub use types::{
    MonoType, Type, TypeContext, TypeError, TypeResult, Unifiable, BOOL_T, FUN, INT_T, LOCATION,
    PROD, SUM, UNIT_T,
};
use types::{MonoTypeResult, TypeUnifier, TypingResult, UNIT};

fn expect_un_op_type(un_op: &UnOp) -> MonoType {
    match un_op {
        UnOp::Neg => BOOL_T,
        UnOp::MinusUn => INT_T,
    }
}

fn expect_bin_op_type(bi_op: &BinOp, ctxt: &mut TypeContext) -> (MonoType, MonoType, MonoType) {
    use MonoType::*;
    match bi_op {
        BinOp::Plus
        | BinOp::Minus
        | BinOp::Mult
        | BinOp::Quot
        | BinOp::Rem
        | BinOp::ShiftL
        | BinOp::ShiftR => (INT_T, INT_T, INT_T),
        BinOp::And | BinOp::Or | BinOp::Xor => (BOOL_T, BOOL_T, BOOL_T),
        BinOp::Le | BinOp::Lt | BinOp::Eq => (INT_T, INT_T, BOOL_T),
        BinOp::Offset => {
            let var = ctxt.new_var();
            (
                MonoType::constr(LOCATION, vec![Free(var)]).unwrap(),
                INT_T,
                MonoType::constr(LOCATION, vec![Free(var)]).unwrap(),
            )
        }
    }
}

fn type_check_lit(lit: &Literal, ctxt: &mut TypeContext) -> MonoTypeResult {
    Ok(match lit {
        Literal::Int(_) => INT_T,
        Literal::Bool(_) => BOOL_T,
        Literal::Unit => UNIT_T,
        Literal::Loc(_) => {
            let var = ctxt.new_var();
            MonoType::constr(LOCATION, vec![MonoType::Free(var)])?
        }
    })
}

fn type_check_lambda(
    fun_name: &Option<String>,
    arg_name: &Option<String>,
    expr: &Expr,
    ctxt: &mut TypeContext,
) -> TypingResult {
    let mut old_fun_type = None;
    let mut old_arg_type = None;
    let body_type_var = ctxt.new_var();
    let arg_type_var = ctxt.new_var();

    let mut fun_type = MonoType::constr(
        FUN,
        vec![MonoType::Free(arg_type_var), MonoType::Free(body_type_var)],
    )?;

    // Shadow old variables with the same name.
    if let Some(fun_name) = fun_name {
        old_fun_type = ctxt.insert(fun_name.clone(), Type::Mono(fun_type.clone()));
    };
    if let Some(arg_name) = arg_name {
        old_arg_type = ctxt.insert(arg_name.clone(), Type::Mono(MonoType::Free(arg_type_var)));
    };

    // Type the body and instantiate the function type with the obtained unifiers.
    let (body_type, unifiers) = type_check(expr, ctxt)?;
    fun_type = MonoType::constr(FUN, vec![MonoType::Free(arg_type_var), body_type])?;
    fun_type.instantiate_from_unifiers(&unifiers);

    // Unshadow the old variables or introduce the new function.
    if let Some(arg_name) = arg_name {
        if let Some(mut old_arg_type) = old_arg_type {
            old_arg_type.instantiate_from_unifiers(&unifiers);
            ctxt.insert(arg_name.clone(), old_arg_type);
        } else {
            ctxt.drop_var(arg_name);
        }
    }

    if let Some(fun_name) = fun_name {
        let mut typ = old_fun_type.unwrap_or_else(|| Type::Mono(fun_type.clone()));
        typ.instantiate_from_unifiers(&unifiers);
        ctxt.insert(fun_name.clone(), typ);
    };

    Ok((fun_type, unifiers))
}

fn type_check_val(val: &Val, ctxt: &mut TypeContext) -> TypingResult {
    match val {
        Val::LitV(lit) => type_check_lit(lit, ctxt).map(|typ| (typ, vec![])),
        Val::RecV {
            fun_name,
            arg_name,
            expr,
        } => type_check_lambda(fun_name, arg_name, expr, ctxt),
        Val::PairV(fst, snd) => {
            let (fst_type, mut unifiers1) = type_check_val(fst, ctxt)?;
            let (snd_type, mut unifiers2) = type_check_val(snd, ctxt)?;
            unifiers1.append(&mut unifiers2);
            MonoType::constr(PROD, vec![fst_type, snd_type]).map(|typ| (typ, unifiers1))
        }
        Val::InjLV(left) => {
            let (left_type, unifiers) = type_check_val(left, ctxt)?;
            MonoType::constr(SUM, vec![left_type, MonoType::Free(ctxt.new_var())])
                .map(|typ| (typ, unifiers))
        }
        Val::InjR(right) => {
            let (right_type, unifiers) = type_check_val(right, ctxt)?;
            MonoType::constr(SUM, vec![MonoType::Free(ctxt.new_var()), right_type])
                .map(|typ| (typ, unifiers))
        }
    }
}

fn type_check_sum(
    sum: &Expr,
    ctxt: &mut TypeContext,
    handler: impl Fn(&MonoType, &MonoType, &mut TypeContext, Vec<TypeUnifier>) -> TypingResult,
) -> TypingResult {
    let (sum_type, unifiers) = type_check(sum, ctxt)?;
    let args = sum_type.args(&SUM)?;
    handler(args.get(0).unwrap(), args.get(1).unwrap(), ctxt, unifiers)
}

pub fn type_check(expr: &Expr, ctxt: &mut TypeContext) -> TypingResult {
    match expr {
        Expr::Val(v) => type_check_val(v, ctxt),
        Expr::Var(v) => ctxt
            .get_type(v)
            .cloned()
            .ok_or(TypeError::VarNotFound)
            .map(|typ| (ctxt.monomorphize(&typ), vec![])),
        Expr::Rec {
            fun_name,
            arg_name,
            expr,
        } => type_check_lambda(fun_name, arg_name, expr, ctxt),
        Expr::App(f_expr, a_expr) => {
            let (mut fun_type, mut unifiers1) = type_check(f_expr, ctxt)?;
            let (arg_type, mut unifiers2) = type_check(a_expr, ctxt)?;

            fun_type.instantiate_from_unifiers(&unifiers2);
            let result_var = ctxt.new_var();
            let fun_type_mgu = MonoType::constr(FUN, vec![arg_type, MonoType::Free(result_var)])?;
            let mgu = fun_type.unify_with(&fun_type_mgu)?;
            ctxt.fix_from_unifier(&mgu);

            mgu.get_or_var(&result_var)
                .ok_or(TypeError::UnificationFailed)
                .map(|typ| {
                    unifiers1.append(&mut unifiers2);
                    unifiers1.push(mgu);
                    (typ, unifiers1)
                })
        }
        Expr::UnOp(un_op, expr) => {
            let expected_type = expect_un_op_type(un_op);
            let (actual_type, mut unifiers) = type_check(expr, ctxt)?;
            let unifier = actual_type.unify_with(&expected_type)?;
            ctxt.fix_from_unifier(&unifier);
            unifiers.push(unifier);
            Ok((expected_type, unifiers))
        }
        Expr::BinOp(bin_op, arg1, arg2) => {
            let (exp_arg1, exp_arg2, res_type) = expect_bin_op_type(bin_op, ctxt);

            let (actual_arg1, mut unifiers1) = type_check(arg1, ctxt)?;
            let unifier1 = actual_arg1.unify_with(&exp_arg1)?;
            ctxt.fix_from_unifier(&unifier1);
            unifiers1.push(unifier1);

            let (actual_arg2, mut unifiers2) = type_check(arg2, ctxt)?;
            let unifier2 = actual_arg2.unify_with(&exp_arg2)?;
            ctxt.fix_from_unifier(&unifier2);
            unifiers2.push(unifier2);

            unifiers1.append(&mut unifiers2);

            Ok((res_type, unifiers1))
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let (cond_type, mut unifiers1) = type_check(condition, ctxt)?;
            // Make sure the condition is a boolean
            let unifier1 = cond_type.unify_with(&BOOL_T)?;
            ctxt.fix_from_unifier(&unifier1);
            unifiers1.push(unifier1);

            let (mut then_type, mut unifiers2) = type_check(then_branch, ctxt)?;
            let (else_type, mut unifiers3) = type_check(else_branch, ctxt)?;

            // Make sure, both branches have the same type
            let unifier2 = then_type.unify_with(&else_type)?;
            then_type.instantiate_from_unifier(&unifier2);
            ctxt.fix_from_unifier(&unifier2);

            unifiers1.append(&mut unifiers2);
            unifiers1.append(&mut unifiers3);
            unifiers1.push(unifier2);

            Ok((then_type, unifiers1))
        }
        Expr::Pair(fst, snd) => {
            let (fst_type, mut unifiers1) = type_check(fst, ctxt)?;
            let (snd_type, mut unifiers2) = type_check(snd, ctxt)?;
            unifiers1.append(&mut unifiers2);
            MonoType::constr(PROD, vec![fst_type, snd_type]).map(|m| (m, unifiers1))
        }
        Expr::Fst(prod) => {
            let (prod_type, mut unifiers) = type_check(prod, ctxt)?;
            let mut expected_prod = MonoType::constr(
                PROD,
                vec![
                    MonoType::Free(ctxt.new_var()),
                    MonoType::Free(ctxt.new_var()),
                ],
            )?;

            let unifier = expected_prod.unify_with(&prod_type)?;
            ctxt.fix_from_unifier(&unifier);
            expected_prod.instantiate_from_unifier(&unifier);
            unifiers.push(unifier);

            expected_prod
                .args(&PROD)?
                .get(0)
                .cloned()
                .ok_or(TypeError::TypeMismatch)
                .map(|m| (m, unifiers))
        }
        Expr::Snd(prod) => {
            let (prod_type, mut unifiers) = type_check(prod, ctxt)?;
            let mut expected_prod = MonoType::constr(
                PROD,
                vec![
                    MonoType::Free(ctxt.new_var()),
                    MonoType::Free(ctxt.new_var()),
                ],
            )?;

            let unifier = expected_prod.unify_with(&prod_type)?;
            ctxt.fix_from_unifier(&unifier);
            expected_prod.instantiate_from_unifier(&unifier);
            unifiers.push(unifier);

            expected_prod
                .args(&PROD)?
                .get(1)
                .cloned()
                .ok_or(TypeError::TypeConstructorArgumentMismatch)
                .map(|m| (m, unifiers))
        }
        Expr::InjL(sum) => type_check_sum(sum, ctxt, |left, _, _, unifiers| {
            Ok((left.clone(), unifiers))
        }),
        Expr::InjR(sum) => type_check_sum(sum, ctxt, |_, right, _, unifiers| {
            Ok((right.clone(), unifiers))
        }),
        Expr::Case {
            match_expr,
            left_name,
            left_case,
            right_name,
            right_case,
        } => {
            type_check_sum(match_expr, ctxt, |l_type, r_type, ctxt, mut unifiers| {
                // Shadow old variables.
                let mut old_left_type = None;
                let mut old_right_type = None;

                if let Some(left_name) = left_name {
                    old_left_type = ctxt.insert(left_name.clone(), Type::Mono(l_type.clone()));
                }
                let (mut l_case_type, mut unifiers1) = type_check(left_case, ctxt)?;
                unifiers.append(&mut unifiers1);
                if let Some(left_name) = left_name {
                    ctxt.drop_var(left_name);
                }

                if let Some(right_name) = right_name {
                    old_right_type = ctxt.insert(right_name.clone(), Type::Mono(r_type.clone()));
                }
                let (r_case_type, mut unifiers2) = type_check(right_case, ctxt)?;
                unifiers.append(&mut unifiers2);

                //Unshadow old variables in reverse order .
                if let Some(right_name) = right_name {
                    if let Some(old_right_type) = old_right_type {
                        ctxt.insert(right_name.clone(), old_right_type);
                    } else {
                        ctxt.drop_var(right_name);
                    }
                }
                if let Some(left_name) = left_name {
                    if let Some(old_left_type) = old_left_type {
                        ctxt.insert(left_name.clone(), old_left_type);
                    }
                }

                // Make sure, both cases produce the same type.
                let unifier = l_case_type.unify_with(&r_case_type)?;
                l_case_type.instantiate_from_unifier(&unifier);
                ctxt.fix_from_unifier(&unifier);
                unifiers.push(unifier);

                Ok((l_case_type, unifiers))
            })
        }
        Expr::Fork(thread) => {
            let (thread_type, mut unifiers) = type_check(thread, ctxt)?;
            let expected_thread_type =
                MonoType::constr(FUN, vec![MonoType::Id(UNIT), MonoType::Id(UNIT)])?;
            let unifier = expected_thread_type.unify_with(&thread_type)?;
            ctxt.fix_from_unifier(&unifier);
            unifiers.push(unifier);

            Ok((expected_thread_type, unifiers))
        }
        Expr::AllocN {
            array_len,
            initial_val,
        } => {
            let (len_type, mut unifiers1) = type_check(array_len, ctxt)?;
            let unifier = len_type.unify_with(&INT_T)?;
            ctxt.fix_from_unifier(&unifier);
            unifiers1.push(unifier);

            let (val_type, mut unifiers2) = type_check(initial_val, ctxt)?;
            unifiers1.append(&mut unifiers2);
            MonoType::constr(LOCATION, vec![val_type]).map(|m| (m, unifiers1))
        }
        Expr::Free(loc) => {
            let (loc_type, mut unifiers) = type_check(loc, ctxt)?;
            let expected_loc_type =
                MonoType::constr(LOCATION, vec![MonoType::Free(ctxt.new_var())])?;
            let unifier = loc_type.unify_with(&expected_loc_type)?;
            ctxt.fix_from_unifier(&unifier);
            unifiers.push(unifier);
            Ok((UNIT_T, unifiers))
        }
        Expr::Load(loc) => {
            let (loc_type, mut unifiers) = type_check(loc, ctxt)?;
            let mut expected_loc_type =
                MonoType::constr(LOCATION, vec![MonoType::Free(ctxt.new_var())])?;
            let unifier = loc_type.unify_with(&expected_loc_type)?;
            ctxt.fix_from_unifier(&unifier);
            expected_loc_type.instantiate_from_unifier(&unifier);
            unifiers.push(unifier);

            expected_loc_type
                .args(&LOCATION)?
                .get(0)
                .cloned()
                .ok_or(TypeError::TypeConstructorArgumentMismatch)
                .map(|m| (m, unifiers))
        }
        Expr::Store(loc, val) => {
            let (stored_type, mut unifiers1) = type_check(val, ctxt)?;
            let (loc_type, mut unifiers2) = type_check(loc, ctxt)?;
            unifiers1.append(&mut unifiers2);

            let expected_loc_type = MonoType::constr(LOCATION, vec![stored_type])?;
            let unifier = loc_type.unify_with(&expected_loc_type)?;
            ctxt.fix_from_unifier(&unifier);
            unifiers1.push(unifier);

            Ok((UNIT_T, unifiers1))
        }
        Expr::CmpXchg {
            location,
            expected_val,
            new_expr_val,
        } => {
            let (mut expected_val_type, mut unifiers1) = type_check(expected_val, ctxt)?;
            let (new_expr_val_type, mut unifiers2) = type_check(new_expr_val, ctxt)?;
            unifiers1.append(&mut unifiers2);

            let unifier1 = expected_val_type.unify_with(&new_expr_val_type)?;
            expected_val_type.instantiate_from_unifier(&unifier1);
            ctxt.fix_from_unifier(&unifier1);
            unifiers1.push(unifier1);

            let (loc_type, mut unifiers3) = type_check(location, ctxt)?;
            unifiers1.append(&mut unifiers3);

            let expected_loc_type = MonoType::constr(LOCATION, vec![expected_val_type])?;
            let unifier2 = loc_type.unify_with(&expected_loc_type)?;
            ctxt.fix_from_unifier(&unifier2);
            unifiers1.push(unifier2);

            Ok((BOOL_T, unifiers1))
        }
        Expr::Xchg {
            location,
            new_expr_val,
        } => {
            let (mut new_expr_val_type, mut unifiers1) = type_check(new_expr_val, ctxt)?;
            let (loc_type, mut unifiers2) = type_check(location, ctxt)?;
            unifiers1.append(&mut unifiers2);

            let expected_loc_type = MonoType::constr(LOCATION, vec![new_expr_val_type.clone()])?;
            let unifier = loc_type.unify_with(&expected_loc_type)?;
            new_expr_val_type.instantiate_from_unifier(&unifier);
            ctxt.fix_from_unifier(&unifier);
            unifiers1.push(unifier);

            Ok((new_expr_val_type, unifiers1))
        }
        Expr::FAA { location, summand } => {
            let (loc_type, mut unifiers1) = type_check(location, ctxt)?;
            let expected_loc_type = MonoType::constr(LOCATION, vec![INT_T])?;
            let unifier = loc_type.unify_with(&expected_loc_type)?;
            ctxt.fix_from_unifier(&unifier);
            unifiers1.push(unifier);

            let (summand_type, mut unifiers2) = type_check(summand, ctxt)?;
            unifiers1.append(&mut unifiers2);

            let unifier = summand_type.unify_with(&INT_T)?;
            ctxt.fix_from_unifier(&unifier);
            unifiers1.push(unifier);

            Ok((INT_T, unifiers1))
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

        let expected_type = BOOL_T;
        let mut ctxt = TypeContext::default();
        let x_var = ctxt.new_var();
        ctxt.insert("x".to_string(), Type::Mono(MonoType::Free(x_var)));
        assert_eq!(expected_type, type_check(&term, &mut ctxt)?.0);

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

        let expected_type = MonoType::constr(FUN, vec![INT_T, UNIT_T])?;
        let mut ctxt = TypeContext::default();
        assert_eq!(expected_type, type_check(&term, &mut ctxt)?.0);

        Ok(())
    }
}
