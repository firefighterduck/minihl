use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq)]
pub struct TypeUnificationError;

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    VarNotFound,
    TypeMismatch,
    TypeNotInferable,
    UnificationFailed,
    OccursCheckFailed,
}

impl From<TypeUnificationError> for TypeError {
    fn from(_: TypeUnificationError) -> Self {
        TypeError::UnificationFailed
    }
}

pub type TypeResult = Result<Type, TypeError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct TypeVar(usize);

impl TypeVar {
    pub fn increase(&mut self) {
        self.0 += 1;
    }

    pub fn normalize(tuple: (TypeVar, TypeVar)) -> (TypeVar, TypeVar) {
        let (TypeVar(v1), TypeVar(v2)) = tuple;
        if v1 > v2 {
            (TypeVar(v2), TypeVar(v1))
        } else {
            tuple
        }
    }
}

/// HeapLang types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    LocationT(Box<Type>),
    IntT,
    BoolT,
    UnitT,
    FunT(Box<Type>, Box<Type>),
    ProdT(Box<Type>, Box<Type>),
    SumT(Box<Type>, Box<Type>),
    Free(TypeVar),
}

#[derive(Debug, PartialEq, Eq, Default)]
pub struct TypeUnifier {
    var_equality: HashMap<TypeVar, TypeVar>,
    instantiations: HashMap<TypeVar, Type>,
}

type UnificationResult = Result<(), TypeUnificationError>;

impl TypeUnifier {
    fn eqalize(&self, var: &TypeVar) -> TypeVar {
        *self.var_equality.get(var).unwrap_or(var)
    }

    pub fn get(&self, var: &TypeVar) -> Option<&Type> {
        let var = self.eqalize(var);
        self.instantiations.get(&var)
    }

    pub fn insert_eq(&mut self, var1: &TypeVar, var2: &TypeVar) -> UnificationResult {
        let var1 = self.eqalize(var1);
        let var2 = self.eqalize(var2);
        let (var1, var2) = TypeVar::normalize((var1, var2));

        self.var_equality.insert(var2, var1);
        for (key, typ) in self.instantiations.iter_mut() {
            if *key == var2 {
                return Err(TypeUnificationError);
            }
            typ.instantiate_var(var2, Type::Free(var1));
        }

        Ok(())
    }

    pub fn insert_inst(&mut self, var: &TypeVar, typ: Type) -> UnificationResult {
        let var = self.eqalize(var);
        if let Some(old_type) = self.instantiations.get(&var) {
            if old_type != &typ {
                Err(TypeUnificationError)
            } else {
                Ok(())
            }
        } else if typ.occurs_check(var) {
            Err(TypeUnificationError)
        } else {
            self.instantiations.insert(var, typ);
            Ok(())
        }
    }

    pub fn is_empty(&self) -> bool {
        self.var_equality.is_empty() && self.instantiations.is_empty()
    }
}

impl Type {
    pub fn occurs_check(&self, var: TypeVar) -> bool {
        match self {
            Type::LocationT(l) => l.occurs_check(var),
            Type::IntT => false,
            Type::BoolT => false,
            Type::UnitT => false,
            Type::FunT(f, a) => f.occurs_check(var) || a.occurs_check(var),
            Type::ProdT(f, s) => f.occurs_check(var) || s.occurs_check(var),
            Type::SumT(l, r) => l.occurs_check(var) || r.occurs_check(var),
            Type::Free(v) => *v == var,
        }
    }

    pub fn instantiate_var(&mut self, var: TypeVar, new_type: Type) {
        match self {
            Type::LocationT(l) => l.instantiate_var(var, new_type),
            Type::IntT => (),
            Type::BoolT => (),
            Type::UnitT => (),
            Type::FunT(fun_type, arg_type) => {
                fun_type.instantiate_var(var, new_type.clone());
                arg_type.instantiate_var(var, new_type)
            }
            Type::ProdT(fst_type, snd_type) => {
                fst_type.instantiate_var(var, new_type.clone());
                snd_type.instantiate_var(var, new_type)
            }
            Type::SumT(injl_type, injr_type) => {
                injl_type.instantiate_var(var, new_type.clone());
                injr_type.instantiate_var(var, new_type)
            }
            Type::Free(v) => {
                if v == &var {
                    *self = new_type;
                }
            }
        }
    }

    pub fn instantiate_from_unifier(&mut self, unifier: &TypeUnifier) {
        match self {
            Type::LocationT(l) => l.instantiate_from_unifier(unifier),
            Type::IntT => (),
            Type::BoolT => (),
            Type::UnitT => (),
            Type::FunT(fun_type, arg_type) => {
                fun_type.instantiate_from_unifier(unifier);
                arg_type.instantiate_from_unifier(unifier);
            }
            Type::ProdT(fst_type, snd_type) => {
                fst_type.instantiate_from_unifier(unifier);
                snd_type.instantiate_from_unifier(unifier)
            }
            Type::SumT(injl_type, injr_type) => {
                injl_type.instantiate_from_unifier(unifier);
                injr_type.instantiate_from_unifier(unifier)
            }
            Type::Free(v) => {
                if let Some(typ) = unifier.get(v) {
                    *self = typ.clone();
                }
            }
        }
    }

    fn unify_rec(&self, other: &Type, unifier: &mut TypeUnifier) -> UnificationResult {
        match (self, other) {
            (Type::Free(v1), Type::Free(v2)) => {
                if v1 == v2 {
                    Ok(())
                } else {
                    match (unifier.get(v1), unifier.get(v2)) {
                        (Some(t1), Some(t2)) => {
                            if t1 == t2 {
                                Ok(())
                            } else {
                                Err(TypeUnificationError)
                            }
                        }
                        (Some(t), _) => unifier.insert_inst(v2, t.clone()),
                        (_, Some(t)) => unifier.insert_inst(v1, t.clone()),
                        _ => unifier.insert_eq(v1, v2),
                    }
                }
            }
            (Type::Free(var), t) => unifier.insert_inst(var, t.clone()),
            (t, Type::Free(var)) => unifier.insert_inst(var, t.clone()),
            (Type::LocationT(l1), Type::LocationT(l2)) => l1.unify_rec(l2, unifier),
            (Type::IntT, Type::IntT) => Ok(()),
            (Type::BoolT, Type::BoolT) => Ok(()),
            (Type::UnitT, Type::UnitT) => Ok(()),
            (Type::FunT(f1, a1), Type::FunT(f2, a2)) => {
                f1.unify_rec(f2, unifier)?;
                a1.unify_rec(a2, unifier)
            }
            (Type::ProdT(f1, s1), Type::ProdT(f2, s2)) => {
                f1.unify_rec(f2, unifier)?;
                s1.unify_rec(s2, unifier)
            }
            (Type::SumT(l1, r1), Type::SumT(l2, r2)) => {
                l1.unify_rec(l2, unifier)?;
                r1.unify_rec(r2, unifier)
            }
            _ => Err(TypeUnificationError),
        }
    }

    pub fn unify(&self, other: &Type) -> Result<TypeUnifier, TypeUnificationError> {
        let mut unifier = TypeUnifier::default();
        self.unify_rec(other, &mut unifier)?;
        Ok(unifier)
    }
}

#[derive(Debug, Default)]
pub struct TypeDict {
    var_dict: HashMap<String, Type>,
    new_var_counter: TypeVar,
}

impl TypeDict {
    pub fn get_type(&self, var: &str) -> Option<&Type> {
        self.var_dict.get(var)
    }

    pub fn new_var(&mut self) -> TypeVar {
        self.new_var_counter.increase();
        self.new_var_counter
    }

    pub fn insert(&mut self, key: String, type_value: Type) -> Option<Type> {
        self.var_dict.insert(key, type_value)
    }

    pub fn fix_type_var(&mut self, var: TypeVar, new_type: Type) {
        debug_assert!(!matches!(new_type, Type::Free(_)));

        for (_, typ) in self.var_dict.iter_mut() {
            typ.instantiate_var(var, new_type.clone());
        }
    }

    pub fn fix_from_unifier(&mut self, unifier: &TypeUnifier) {
        for (_, typ) in self.var_dict.iter_mut() {
            typ.instantiate_from_unifier(unifier);
        }
    }

    pub fn drop_var(&mut self, var: &String) {
        self.var_dict.remove(var);
    }

    /// Checks whether a variable has already the expected type or fixes it otherwise.
    pub fn check_or_fix_type(&mut self, var: &String, mut expected_type: Type) -> TypeResult {
        if let Some(actual_type) = self.var_dict.get(var) {
            // The variable already has an associated type.
            let unifier = actual_type.unify(&expected_type)?;
            // The associated type can be unified with the expected type.
            if !unifier.is_empty() {
                // We acquired new information about free variables and use them to update the dict.
                for (_, typ) in self.var_dict.iter_mut() {
                    typ.instantiate_from_unifier(&unifier);
                }

                expected_type.instantiate_from_unifier(&unifier);
            }

            Ok(expected_type)
        } else {
            // The varable has no assicated type yet, so we set the expected type as such.
            self.var_dict.insert(var.clone(), expected_type.clone());
            Ok(expected_type)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_occurs_check() {
        use Type::*;
        let var = TypeVar(12);

        let occurs = FunT(
            Box::new(SumT(Box::new(Free(TypeVar(2))), Box::new(BoolT))),
            Box::new(ProdT(
                Box::new(Free(TypeVar(12))),
                Box::new(LocationT(Box::new(UnitT))),
            )),
        );
        let not_occurs = FunT(
            Box::new(SumT(Box::new(Free(TypeVar(2))), Box::new(BoolT))),
            Box::new(ProdT(
                Box::new(Free(TypeVar(11))),
                Box::new(LocationT(Box::new(UnitT))),
            )),
        );

        assert!(occurs.occurs_check(var));
        assert_eq!(not_occurs.occurs_check(var), false);
    }

    #[test]
    fn test_unify() -> UnificationResult {
        use Type::*;

        let var1 = TypeVar(2);
        let var2 = TypeVar(3);
        let var3 = TypeVar(12);

        let full_type = FunT(
            Box::new(SumT(Box::new(UnitT), Box::new(BoolT))),
            Box::new(ProdT(Box::new(UnitT), Box::new(LocationT(Box::new(UnitT))))),
        );

        let mut t1 = FunT(
            Box::new(SumT(Box::new(Free(var1)), Box::new(BoolT))),
            Box::new(ProdT(
                Box::new(Free(var3)),
                Box::new(LocationT(Box::new(UnitT))),
            )),
        );
        let mut t2 = FunT(
            Box::new(SumT(Box::new(UnitT), Box::new(Free(var2)))),
            Box::new(ProdT(
                Box::new(Free(var1)),
                Box::new(LocationT(Box::new(UnitT))),
            )),
        );

        let unifier = t1.unify(&t2)?;

        t1.instantiate_from_unifier(&unifier);
        t2.instantiate_from_unifier(&unifier);

        assert_eq!(t1, full_type);
        assert_eq!(t2, full_type);

        Ok(())
    }

    #[test]
    fn test_check_or_fix() -> Result<(), TypeError> {
        use Type::*;

        let mut dict = TypeDict::default();
        let var1 = "x".to_string();
        let var2 = "y".to_string();
        let type_var1 = dict.new_var();
        let type_var2 = dict.new_var();

        let type1 = FunT(Box::new(Free(type_var1)), Box::new(Free(type_var2)));
        let type2 = FunT(Box::new(BoolT), Box::new(Free(type_var2)));
        let type3 = SumT(Box::new(Free(type_var1)), Box::new(UnitT));

        // Not yet fixed type for var.
        let t = dict.check_or_fix_type(&var1, type1.clone())?;
        assert_eq!(t, type1);

        let t = dict.check_or_fix_type(&var2, type3.clone())?;
        assert_eq!(t, type3);

        // Unify stored and given type.
        let t = dict.check_or_fix_type(&var1, type2.clone())?;
        assert_eq!(t, type2);

        // Check other stored type that is now refined.
        let t = dict.get_type(&var2).cloned();
        assert_eq!(t, Some(SumT(Box::new(BoolT), Box::new(UnitT))));

        // Empty unifier.
        let t = dict.check_or_fix_type(&var1, type2.clone())?;
        assert_eq!(t, type2);

        Ok(())
    }
}
