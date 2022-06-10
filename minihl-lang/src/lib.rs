#![feature(box_patterns)]
#![feature(let_chains)]

mod abbreviations;
mod interpret;
mod lang_defs;
mod type_check;
mod types;

pub use abbreviations::{
    alloc, cas, lambda_expr, lambda_val, let_in, match_expr, match_opt, none_expr, none_val, seq,
    some_expr, some_val,
};
pub use interpret::{EvalResult, RuntimeError, State};
pub use lang_defs::{BinOp, Expr, Literal, UnOp, Val};
pub use type_check::{type_check, type_check_val};
pub use types::{
    MonoType, Type, TypeContext, TypeError, TypeResult, Unifiable, BOOL_T, FUN, INT_T, LOCATION,
    PROD, SUM, UNIT_T,
};
