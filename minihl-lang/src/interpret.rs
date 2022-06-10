use std::{
    collections::HashMap,
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub},
};

macro_rules! bin_op {
    ($id1:ident,$id2:ident, $constr1_in:ident, $constr2_in:ident, $constr_out: ident, $op:ident) => {
        if let (Val::LitV($constr1_in(x)), Val::LitV($constr2_in(y))) = ($id1, $id2) {
            return Ok(Val::LitV($constr_out(x.$op(y))));
        }
    };
}

macro_rules! bin_op_ref {
    ($id1:ident,$id2:ident, $constr1_in:ident, $constr2_in:ident, $constr_out: ident, $op:ident) => {
        if let (Val::LitV($constr1_in(x)), Val::LitV($constr2_in(y))) = ($id1, $id2) {
            return Ok(Val::LitV($constr_out(x.$op(&y))));
        }
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RuntimeError;
pub type EvalResult = Result<Val, RuntimeError>;

use crate::{
    lang_defs::{Binder, Loc},
    BinOp, Expr, Literal, UnOp, Val,
};
use rust_examples::brands::{BrandedIndex, BrandedVec};

pub struct State<'id> {
    variables: HashMap<String, Val>,
    loc_map: HashMap<Loc, BrandedIndex<'id>>,
    highest_loc: usize,
    shadowed: Vec<(String, Option<Val>)>,
    heap: BrandedVec<'id, Option<Val>>,
}

impl<'id> State<'id> {
    pub fn run(expr: Expr) -> EvalResult {
        BrandedVec::make(vec![], move |heap| {
            let mut state = State {
                variables: HashMap::new(),
                loc_map: HashMap::new(),
                highest_loc: expr.highest_loc(),
                shadowed: Vec::new(),
                heap,
            };
            state.eval_expr(expr)
        })
    }

    fn shadow(&mut self, var: &Binder, val: &Val) {
        if let Some(var) = var {
            let old = self.variables.insert(var.clone(), val.clone());
            self.shadowed.push((var.clone(), old));
        }
    }

    fn unshadow(&mut self, var: &Binder) {
        if let Some(var) = var {
            if let Some((shadowed, old)) = self.shadowed.pop() {
                if var == &shadowed && let Some(old) = old{
                    self.variables.insert(shadowed, old);
                }
            }
        }
    }

    fn call_fun(&mut self, fun: Val, arg: Val) -> EvalResult {
        let fun_clone = fun.clone();
        if let Val::RecV {
            fun_name,
            arg_name,
            expr,
        } = fun
        {
            self.shadow(&fun_name, &fun_clone);
            self.shadow(&arg_name, &arg);

            let result = self.eval_expr(*expr);

            self.unshadow(&arg_name);
            self.unshadow(&fun_name);

            result
        } else {
            Err(RuntimeError)
        }
    }

    fn eval_un_op(&self, op: UnOp, arg: Val) -> EvalResult {
        match op {
            UnOp::Neg => {
                if let Val::LitV(Literal::Bool(b)) = arg {
                    Ok(Val::LitV(Literal::Bool(!b)))
                } else {
                    Err(RuntimeError)
                }
            }
            UnOp::MinusUn => {
                if let Val::LitV(Literal::Int(i)) = arg {
                    Ok(Val::LitV(Literal::Int(-i)))
                } else {
                    Err(RuntimeError)
                }
            }
        }
    }

    fn eval_bin_op(&self, op: BinOp, arg1: Val, arg2: Val) -> EvalResult {
        use Literal::*;
        match op {
            BinOp::Plus => bin_op!(arg1, arg2, Int, Int, Int, add),
            BinOp::Minus => bin_op!(arg1, arg2, Int, Int, Int, sub),
            BinOp::Mult => bin_op!(arg1, arg2, Int, Int, Int, mul),
            BinOp::Quot => bin_op!(arg1, arg2, Int, Int, Int, div),
            BinOp::Rem => bin_op!(arg1, arg2, Int, Int, Int, rem),
            BinOp::And => bin_op!(arg1, arg2, Bool, Bool, Bool, bitand),
            BinOp::Or => bin_op!(arg1, arg2, Bool, Bool, Bool, bitor),
            BinOp::Xor => bin_op!(arg1, arg2, Bool, Bool, Bool, bitxor),
            BinOp::ShiftL => bin_op!(arg1, arg2, Int, Int, Int, shl),
            BinOp::ShiftR => bin_op!(arg1, arg2, Int, Int, Int, shr),
            BinOp::Le => bin_op_ref!(arg1, arg2, Int, Int, Bool, le),
            BinOp::Lt => bin_op_ref!(arg1, arg2, Int, Int, Bool, lt),
            BinOp::Eq => bin_op_ref!(arg1, arg2, Int, Int, Bool, eq),
            BinOp::Offset => bin_op!(arg1, arg2, Loc, Int, Loc, offset),
        }
        Err(RuntimeError)
    }

    fn eval_expr(&mut self, expr: Expr) -> EvalResult {
        match expr {
            Expr::Val(v) => Ok((*v).clone()),
            Expr::Var(v) => self.variables.get(&v).cloned().ok_or(RuntimeError),
            Expr::Rec {
                fun_name,
                arg_name,
                expr,
            } => {
                let fun_val = Val::RecV {
                    fun_name: fun_name.clone(),
                    arg_name,
                    expr,
                };
                self.shadow(&fun_name, &fun_val);
                Ok(fun_val)
            }
            Expr::App(fun, arg) => {
                let fun = self.eval_expr(*fun)?;
                let arg = self.eval_expr(*arg)?;
                self.call_fun(fun, arg)
            }
            Expr::UnOp(op, arg) => {
                let arg = self.eval_expr(*arg)?;
                self.eval_un_op(op, arg)
            }
            Expr::BinOp(op, arg1, arg2) => {
                let arg1 = self.eval_expr(*arg1)?;
                let arg2 = self.eval_expr(*arg2)?;
                self.eval_bin_op(op, arg1, arg2)
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.eval_expr(*condition)?;
                if let Val::LitV(Literal::Bool(b)) = condition {
                    if b {
                        self.eval_expr(*then_branch)
                    } else {
                        self.eval_expr(*else_branch)
                    }
                } else {
                    Err(RuntimeError)
                }
            }
            Expr::Pair(fst, snd) => {
                let fst = self.eval_expr(*fst)?;
                let snd = self.eval_expr(*snd)?;
                Ok(Val::PairV(Box::new(fst), Box::new(snd)))
            }
            Expr::Fst(prod) => {
                if let Val::PairV(fst, _) = self.eval_expr(*prod)? {
                    Ok(*fst)
                } else {
                    Err(RuntimeError)
                }
            }
            Expr::Snd(prod) => {
                if let Val::PairV(_, snd) = self.eval_expr(*prod)? {
                    Ok(*snd)
                } else {
                    Err(RuntimeError)
                }
            }
            Expr::InjL(expr) => self.eval_expr(*expr).map(|val| Val::InjLV(Box::new(val))),
            Expr::InjR(expr) => self.eval_expr(*expr).map(|val| Val::InjRV(Box::new(val))),
            Expr::Case {
                match_expr,
                left_case,
                right_case,
            } => {
                let match_expr = self.eval_expr(*match_expr)?;
                match match_expr {
                    Val::InjLV(val) => {
                        let body = self.eval_expr(*left_case)?;
                        self.call_fun(body, *val)
                    }
                    Val::InjRV(val) => {
                        let body = self.eval_expr(*right_case)?;
                        self.call_fun(body, *val)
                    }
                    _ => Err(RuntimeError),
                }
            }
            Expr::Fork(_) => todo!(),
            Expr::AllocN {
                array_len,
                initial_val,
            } => {
                if let Val::LitV(Literal::Int(n)) = self.eval_expr(*array_len)? && n>0 {
                    let initial_val = self.eval_expr(*initial_val)?;
                    let location= self.heap.push(Some(initial_val.clone()));

                    for _ in 1..n {
                        self.heap.push(Some(initial_val.clone()));
                    }

                    self.highest_loc += 1;
                    let loc = Loc::new(self.highest_loc);
                    self.loc_map.insert(loc, location);

                    Ok(Val::LitV(Literal::Loc(loc)))
                } else {
                    Err(RuntimeError)
                }
            }
            Expr::Free(loc) => {
                if let Val::LitV(Literal::Loc(loc)) = self.eval_expr(*loc)? {
                    let index = self.loc_map.get(&loc).ok_or(RuntimeError)?;
                    *self.heap.get_mut(*index) = None;
                    Ok(Val::LitV(Literal::Unit))
                } else {
                    Err(RuntimeError)
                }
            },
            Expr::Load(loc) => {
                if let Val::LitV(Literal::Loc(loc)) = self.eval_expr(*loc)? {
                    let index = self.loc_map.get(&loc).ok_or(RuntimeError)?;
                    if let Some(val) = self.heap.get(*index) {
                        return Ok(val.clone());
                    }
                }
                Err(RuntimeError)
            },
            Expr::Store(loc, val) =>  {
                if let Val::LitV(Literal::Loc(loc)) = self.eval_expr(*loc)? {
                    let val = self.eval_expr(*val)?;
                    let index = self.loc_map.get(&loc).ok_or(RuntimeError)?;
                    *self.heap.get_mut(*index) = Some(val);
                    Ok(Val::LitV(Literal::Unit))
                } else {
                    Err(RuntimeError)
                }
            },
            Expr::CmpXchg {
                location,
                expected_val,
                new_expr_val,
            } => {
                if let Val::LitV(Literal::Loc(loc)) = self.eval_expr(*location)? {
                    let expected_val = self.eval_expr(*expected_val)?;
                    let new_expr_val = self.eval_expr(*new_expr_val)?;
                    let index = self.loc_map.get(&loc).ok_or(RuntimeError)?;
                    let cell = self.heap.get_mut(*index);
                    if let Some(cell) = cell {
                        let old_cell = cell.clone();
                        if cell == &expected_val {
                            *cell = new_expr_val;
                            Ok(Val::PairV(Box::new(old_cell),Box::new(Val::LitV(Literal::Bool(true)))))
                        } else {
                            Ok(Val::PairV(Box::new(old_cell),Box::new(Val::LitV(Literal::Bool(false)))))
                        }
                    } else {
                        Err(RuntimeError)
                    }
                } else {
                    Err(RuntimeError)
                }
            },
            Expr::Xchg {
                location,
                new_expr_val,
            } => {
                if let Val::LitV(Literal::Loc(loc)) = self.eval_expr(*location)? {
                    let new_expr_val = self.eval_expr(*new_expr_val)?;
                    let index = self.loc_map.get(&loc).ok_or(RuntimeError)?;
                    let cell = self.heap.get_mut(*index);
                    if let Some(cell) = cell {
                            let old_cell = cell.clone();
                            *cell = new_expr_val;
                            Ok(old_cell)
                    } else {
                        Err(RuntimeError)
                    }
                } else {
                    Err(RuntimeError)
                }
            },
            Expr::FAA { location, summand } => {
                if let Val::LitV(Literal::Loc(loc)) = self.eval_expr(*location)? &&
                    let Val::LitV(Literal::Int(summand)) = self.eval_expr(*summand)?{
                    let index = self.loc_map.get(&loc).ok_or(RuntimeError)?;
                    let cell = self.heap.get_mut(*index);
                    if let Some(Val::LitV(Literal::Int(i))) = cell {
                        *i+=summand;
                        Ok(Val::LitV(Literal::Int(*i)))
                    } else {
                        Err(RuntimeError)
                    }
                } else {
                    Err(RuntimeError)
                }
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_run() -> Result<(), RuntimeError> {
        let fun = Expr::Rec {
            fun_name: Some("f".to_string()),
            arg_name: Some("x".to_string()),
            expr: Box::new(Expr::If {
                condition: Box::new(Expr::BinOp(
                    BinOp::Lt,
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(3))))),
                )),
                then_branch: Box::new(Expr::BinOp(
                    BinOp::Mult,
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(7))))),
                )),
                else_branch: Box::new(Expr::App(
                    Box::new(Expr::Var("f".to_string())),
                    Box::new(Expr::BinOp(
                        BinOp::Minus,
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(1))))),
                    )),
                )),
            }),
        };
        let term1 = Expr::App(
            Box::new(fun.clone()),
            Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(-1))))),
        );
        let term2 = Expr::App(
            Box::new(fun),
            Box::new(Expr::Val(Box::new(Val::LitV(Literal::Int(4))))),
        );

        assert_eq!(State::run(term1)?, Val::LitV(Literal::Int(-7)));
        assert_eq!(State::run(term2)?, Val::LitV(Literal::Int(14)));
        Ok(())
    }
}
