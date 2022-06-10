use std::collections::{HashMap, HashSet};

#[derive(Debug, PartialEq, Eq)]
pub struct TypeUnificationError;

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    VarNotFound,
    TypeMismatch,
    TypeConstructorArgumentMismatch,
    TypeNotInferable,
    UnificationFailed,
    OccursCheckFailed,
    MonomorphizationFailed,
}

impl From<TypeUnificationError> for TypeError {
    fn from(_: TypeUnificationError) -> Self {
        TypeError::UnificationFailed
    }
}

pub type TypeResult = Result<Type, TypeError>;
pub type MonoTypeResult = Result<MonoType, TypeError>;
pub type TypingResult = Result<(MonoType, Vec<TypeUnifier>), TypeError>;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeIdentifier {
    identifier: &'static str,
    arity: usize,
}

impl TypeIdentifier {
    pub const fn atom(identifier: &'static str) -> Self {
        TypeIdentifier {
            identifier,
            arity: 0,
        }
    }
}

/// Hindley-Milner mono-types for HeapLang.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MonoType {
    Id(TypeIdentifier),
    Free(TypeVar),
    Constr {
        constr: TypeIdentifier,
        arguments: Vec<MonoType>,
    },
}

/// Hindley-Milner poly-types for HeapLang.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Mono(MonoType),
    Poly { var: TypeVar, body: Box<Type> },
}

pub const INT: TypeIdentifier = TypeIdentifier::atom("int");
pub const LOCATION: TypeIdentifier = TypeIdentifier {
    identifier: "loc",
    arity: 1,
};
pub const BOOL: TypeIdentifier = TypeIdentifier::atom("bool");
pub const UNIT: TypeIdentifier = TypeIdentifier::atom("()");
pub const FUN: TypeIdentifier = TypeIdentifier {
    identifier: "fun",
    arity: 2,
};
pub const PROD: TypeIdentifier = TypeIdentifier {
    identifier: "prod",
    arity: 2,
};
pub const SUM: TypeIdentifier = TypeIdentifier {
    identifier: "sum",
    arity: 2,
};

pub const INT_T: MonoType = MonoType::Id(INT);
pub const BOOL_T: MonoType = MonoType::Id(BOOL);
pub const UNIT_T: MonoType = MonoType::Id(UNIT);

#[derive(Debug, PartialEq, Eq, Default)]
pub struct TypeUnifier {
    var_equality: HashMap<TypeVar, TypeVar>,
    instantiations: HashMap<TypeVar, MonoType>,
}

type UnificationResult = Result<(), TypeUnificationError>;

impl TypeUnifier {
    fn eqalize(&self, var: &TypeVar) -> TypeVar {
        *self.var_equality.get(var).unwrap_or(var)
    }

    pub fn get(&self, var: &TypeVar) -> Option<&MonoType> {
        let var = self.eqalize(var);
        self.instantiations.get(&var)
    }

    pub fn get_or_var(&self, var: &TypeVar) -> Option<MonoType> {
        if let Some(var) = self.var_equality.get(var) {
            self.instantiations
                .get(var)
                .cloned()
                .or(Some(MonoType::Free(*var)))
        } else {
            self.instantiations.get(var).cloned()
        }
    }

    pub fn insert_eq_raw(&mut self, var1: &TypeVar, var2: &TypeVar) {
        self.var_equality.insert(*var1, *var2);
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
            typ.instantiate_var(&var2, MonoType::Free(var1));
        }

        Ok(())
    }

    pub fn insert_inst(&mut self, var: &TypeVar, mut typ: MonoType) -> UnificationResult {
        let var = self.eqalize(var);
        typ.instantiate_from_unifier(self);

        if let Some(old_type) = self.instantiations.get(&var) {
            if old_type != &typ {
                Err(TypeUnificationError)
            } else {
                Ok(())
            }
        } else if typ.occurs_check(&var) {
            Err(TypeUnificationError)
        } else {
            self.instantiations.insert(var, typ);
            Ok(())
        }
    }

    pub fn is_empty(&self) -> bool {
        self.var_equality.is_empty() && self.instantiations.is_empty()
    }

    pub fn unifies(&self, var: &TypeVar) -> bool {
        self.instantiations.contains_key(var) || self.var_equality.values().any(|v| v == var)
    }
}

pub trait Unifiable
where
    Self: Sized,
{
    fn occurs_check(&self, in_var: &TypeVar) -> bool;
    fn instantiate_var(&mut self, in_var: &TypeVar, new_type: MonoType);
    fn instantiate_from_unifier(&mut self, unifier: &TypeUnifier);
    fn unify(&self, other: &Self, unifier: &mut TypeUnifier) -> UnificationResult;

    fn instantiate_from_unifiers(&mut self, unifiers: &[TypeUnifier]) {
        for unifier in unifiers.iter() {
            self.instantiate_from_unifier(unifier);
        }
    }
    fn unify_with(&self, other: &Self) -> Result<TypeUnifier, TypeUnificationError> {
        let mut unifier = TypeUnifier::default();
        self.unify(other, &mut unifier)?;
        Ok(unifier)
    }
}

trait HasFreeVariables {
    fn free_vars(&self) -> HashSet<TypeVar>;
}

impl MonoType {
    pub fn constr(identfier: TypeIdentifier, arguments: Vec<MonoType>) -> MonoTypeResult {
        if identfier.arity != arguments.len() {
            Err(TypeError::TypeConstructorArgumentMismatch)
        } else {
            Ok(MonoType::Constr {
                constr: identfier,
                arguments,
            })
        }
    }

    fn frees(&self, var_set: &mut HashSet<TypeVar>) {
        match self {
            MonoType::Id(_) => (),
            MonoType::Free(v) => {
                var_set.insert(*v);
            }
            MonoType::Constr { arguments, .. } => {
                arguments.iter().for_each(|arg| arg.frees(var_set))
            }
        }
    }

    pub fn args(&self, identfier: &TypeIdentifier) -> Result<&[MonoType], TypeError> {
        if let MonoType::Constr { constr, arguments } = self && constr==identfier {
            Ok(arguments)
        } else {Err(TypeError::TypeMismatch)}
    }

    pub fn polymorphize(self) -> Type {
        let frees = self.free_vars();
        let mut poly = Type::Mono(self);
        for var in frees {
            poly = Type::Poly {
                var,
                body: Box::new(poly),
            };
        }
        poly
    }
}

impl Unifiable for MonoType {
    fn occurs_check(&self, in_var: &TypeVar) -> bool {
        match self {
            MonoType::Id(_) => false,
            MonoType::Free(v) => v == in_var,
            MonoType::Constr { arguments, .. } => {
                arguments.iter().any(|arg| arg.occurs_check(in_var))
            }
        }
    }

    fn instantiate_var(&mut self, in_var: &TypeVar, new_type: MonoType) {
        match self {
            MonoType::Id(_) => (),
            MonoType::Free(v) => {
                if v == in_var {
                    *self = new_type;
                }
            }
            MonoType::Constr { arguments, .. } => arguments
                .iter_mut()
                .for_each(|arg| arg.instantiate_var(in_var, new_type.clone())),
        }
    }

    fn instantiate_from_unifier(&mut self, unifier: &TypeUnifier) {
        match self {
            MonoType::Free(v) => {
                if let Some(typ) = unifier.get_or_var(v) {
                    *self = typ;
                }
            }
            MonoType::Id(_) => (),
            MonoType::Constr { arguments, .. } => arguments
                .iter_mut()
                .for_each(|arg| arg.instantiate_from_unifier(unifier)),
        }
    }

    fn unify(&self, other: &MonoType, unifier: &mut TypeUnifier) -> UnificationResult {
        use MonoType::*;
        match (self, other) {
            (Free(v1), Free(v2)) => {
                if v1 == v2 {
                    Ok(())
                } else {
                    match (unifier.get_or_var(v1), unifier.get_or_var(v2)) {
                        (Some(t1), Some(t2)) => {
                            // TODO: check whether the instantiations are unifiable
                            if t1 == t2 {
                                Ok(())
                            } else {
                                Err(TypeUnificationError)
                            }
                        }
                        (Some(t), _) => unifier.insert_inst(v2, t),
                        (_, Some(t)) => unifier.insert_inst(v1, t),
                        _ => unifier.insert_eq(v1, v2),
                    }
                }
            }
            (Free(var), t) | (t, Free(var)) => unifier.insert_inst(var, t.clone()),
            (Id(id1), Id(id2)) => {
                if id1 == id2 {
                    Ok(())
                } else {
                    Err(TypeUnificationError)
                }
            }
            (
                Constr {
                    constr: constr1,
                    arguments: arguments1,
                },
                Constr {
                    constr: constr2,
                    arguments: arguments2,
                },
            ) => {
                if constr1 == constr2 && arguments1.len() == arguments2.len() {
                    arguments1
                        .iter()
                        .zip(arguments2.iter())
                        .try_for_each(|(type1, type2)| type1.unify(type2, unifier))
                } else {
                    Err(TypeUnificationError)
                }
            }
            _ => Err(TypeUnificationError),
        }
    }
}

impl HasFreeVariables for MonoType {
    fn free_vars(&self) -> HashSet<TypeVar> {
        let mut var_set = HashSet::new();
        self.frees(&mut var_set);
        var_set
    }
}

impl Unifiable for Type {
    fn occurs_check(&self, in_var: &TypeVar) -> bool {
        match self {
            Type::Mono(m) => m.occurs_check(in_var),
            Type::Poly { var, body } => {
                if var != in_var {
                    body.occurs_check(in_var)
                } else {
                    false
                }
            }
        }
    }

    fn instantiate_var(&mut self, in_var: &TypeVar, new_type: MonoType) {
        match self {
            Type::Mono(m) => m.instantiate_var(in_var, new_type),
            Type::Poly { var, body } => {
                if var != in_var {
                    body.instantiate_var(in_var, new_type)
                }
            }
        }
    }

    fn instantiate_from_unifier(&mut self, unifier: &TypeUnifier) {
        match self {
            Type::Mono(m) => m.instantiate_from_unifier(unifier),
            Type::Poly { var, body } => {
                if !unifier.unifies(var) {
                    body.instantiate_from_unifier(unifier)
                }
            }
        }
    }

    fn unify(&self, other: &Type, unifier: &mut TypeUnifier) -> UnificationResult {
        // TODO: Unify also with instantiation, i.e. if one type is an instance of the other.
        match (self, other) {
            (Type::Mono(m1), Type::Mono(m2)) => m1.unify(m2, unifier),
            (
                Type::Poly {
                    var: var1,
                    body: body1,
                },
                Type::Poly {
                    var: var2,
                    body: body2,
                },
            ) => {
                if var1 != var2 {
                    unifier.insert_eq(var1, var2)?;
                }
                body1.unify(body2, unifier)
            }
            _ => Err(TypeUnificationError),
        }
    }
}

impl HasFreeVariables for Type {
    fn free_vars(&self) -> HashSet<TypeVar> {
        match self {
            Type::Mono(m) => m.free_vars(),
            Type::Poly { var, body } => {
                let mut frees = body.free_vars();
                frees.remove(var);
                frees
            }
        }
    }
}

impl Type {
    pub fn try_monomorphize(self) -> MonoTypeResult {
        match self {
            Type::Mono(m) => Ok(m),
            Type::Poly { .. } => Err(TypeError::MonomorphizationFailed),
        }
    }
}

#[derive(Debug, Default)]
pub struct TypeContext {
    term_var_dict: HashMap<String, Type>,
    new_var_counter: TypeVar,
}

impl HasFreeVariables for TypeContext {
    fn free_vars(&self) -> HashSet<TypeVar> {
        let mut var_set = HashSet::new();
        for (_, ty) in self.term_var_dict.iter() {
            var_set.extend(&ty.free_vars());
        }
        var_set
    }
}

impl TypeContext {
    pub fn get_type(&self, var: &str) -> Option<&Type> {
        self.term_var_dict.get(var)
    }

    pub fn new_var(&mut self) -> TypeVar {
        self.new_var_counter.increase();
        self.new_var_counter
    }

    pub fn insert(&mut self, key: String, type_value: Type) -> Option<Type> {
        self.term_var_dict.insert(key, type_value)
    }

    pub fn fix_from_unifier(&mut self, unifier: &TypeUnifier) {
        for (_, typ) in self.term_var_dict.iter_mut() {
            typ.instantiate_from_unifier(unifier);
        }
    }

    pub fn fix_from_unifiers(&mut self, unifiers: &[TypeUnifier]) {
        for unifier in unifiers.iter() {
            self.fix_from_unifier(unifier);
        }
    }

    pub fn drop_var(&mut self, var: &String) {
        self.term_var_dict.remove(var);
    }

    pub fn monomorphize(&mut self, mut poly: &Type) -> MonoType {
        let mut instantiator = TypeUnifier::default();
        while let Type::Poly { var, body } = poly {
            instantiator
                .insert_inst(var, MonoType::Free(self.new_var()))
                .unwrap();
            poly = body;
        }
        if let Type::Mono(m) = poly {
            let mut mono = m.clone();
            mono.instantiate_from_unifier(&instantiator);
            mono
        } else {
            unreachable!()
        }
    }

    pub fn generalize(&self, typ: MonoType) -> Type {
        let typ_frees = typ.free_vars();
        let ctxt_frees = self.free_vars();
        let remaining = typ_frees.difference(&ctxt_frees);

        let mut poly = Type::Mono(typ);

        for free in remaining {
            poly = Type::Poly {
                var: *free,
                body: Box::new(poly),
            };
        }

        poly
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_inst_poly_type() -> Result<(), TypeError> {
        use Type::*;
        let poly = Poly {
            var: TypeVar(2),
            body: Box::new(Poly {
                var: TypeVar(3),
                body: Box::new(Mono(MonoType::constr(
                    FUN,
                    vec![
                        INT_T,
                        MonoType::constr(
                            SUM,
                            vec![MonoType::Free(TypeVar(2)), MonoType::Free(TypeVar(3))],
                        )?,
                    ],
                )?)),
            }),
        };
        let expected_mono = MonoType::constr(
            FUN,
            vec![
                INT_T,
                MonoType::constr(
                    SUM,
                    vec![MonoType::Free(TypeVar(4)), MonoType::Free(TypeVar(5))],
                )?,
            ],
        )?;
        let mut ctxt = TypeContext::default();
        ctxt.new_var_counter = TypeVar(3);
        assert_eq!(ctxt.monomorphize(&poly), expected_mono);
        Ok(())
    }

    #[test]
    fn test_polymorphize() {
        let mono = MonoType::Constr {
            constr: SUM,
            arguments: vec![MonoType::Free(TypeVar(3)), MonoType::Id(INT)],
        };
        let poly = Type::Poly {
            var: TypeVar(3),
            body: Box::new(Type::Mono(mono.clone())),
        };
        assert_eq!(poly, mono.polymorphize());
    }

    #[test]
    fn test_unify() -> UnificationResult {
        let mut type1 = MonoType::Constr {
            constr: FUN,
            arguments: vec![
                MonoType::Constr {
                    constr: SUM,
                    arguments: vec![MonoType::Free(TypeVar(3)), BOOL_T],
                },
                MonoType::Free(TypeVar(21)),
            ],
        };
        let mut type2 = MonoType::Constr {
            constr: FUN,
            arguments: vec![
                MonoType::Constr {
                    constr: SUM,
                    arguments: vec![INT_T, BOOL_T],
                },
                MonoType::Constr {
                    constr: PROD,
                    arguments: vec![UNIT_T, MonoType::Free(TypeVar(3))],
                },
            ],
        };
        let unified = MonoType::Constr {
            constr: FUN,
            arguments: vec![
                MonoType::Constr {
                    constr: SUM,
                    arguments: vec![INT_T, BOOL_T],
                },
                MonoType::Constr {
                    constr: PROD,
                    arguments: vec![UNIT_T, INT_T],
                },
            ],
        };

        // Occurs check fails.
        let not_unifiable1 = MonoType::Constr {
            constr: FUN,
            arguments: vec![
                MonoType::Constr {
                    constr: SUM,
                    arguments: vec![MonoType::Free(TypeVar(21)), BOOL_T],
                },
                MonoType::Constr {
                    constr: PROD,
                    arguments: vec![UNIT_T, MonoType::Free(TypeVar(3))],
                },
            ],
        };
        let err1 = type1.unify_with(&not_unifiable1);
        assert_eq!(err1, Err(TypeUnificationError));

        // Different values for the same type variable
        let not_unifiable2 = MonoType::Constr {
            constr: FUN,
            arguments: vec![
                MonoType::Constr {
                    constr: SUM,
                    arguments: vec![INT_T, MonoType::Free(TypeVar(3))],
                },
                MonoType::Constr {
                    constr: PROD,
                    arguments: vec![UNIT_T, MonoType::Free(TypeVar(3))],
                },
            ],
        };
        let err2 = type1.unify_with(&not_unifiable2);
        assert_eq!(err2, Err(TypeUnificationError));

        let unifier1 = type1.unify_with(&type2)?;
        let unifier2 = type1.unify_with(&unified)?;
        let unifier3 = type2.unify_with(&type1)?;
        assert_eq!(unifier1, unifier2);
        assert_eq!(unifier1, unifier3);

        type1.instantiate_from_unifier(&unifier1);
        assert_eq!(type1, unified);

        type2.instantiate_from_unifier(&unifier3);
        assert_eq!(type2, unified);

        Ok(())
    }

    #[test]
    fn test_generalize() {
        let mut ctxt = TypeContext::default();
        let bound_var = TypeVar(12);
        let free_var1 = TypeVar(21);
        let free_var2 = TypeVar(7);
        let typ = Type::Poly {
            var: bound_var,
            body: Box::new(Type::Mono(MonoType::Constr {
                constr: SUM,
                arguments: vec![MonoType::Free(bound_var), MonoType::Free(free_var1)],
            })),
        };
        assert_eq!(None, ctxt.insert("x".to_string(), typ));

        let mono = MonoType::Constr {
            constr: FUN,
            arguments: vec![MonoType::Free(free_var1), MonoType::Free(free_var2)],
        };
        let generalized = Type::Poly {
            var: free_var2,
            body: Box::new(Type::Mono(mono.clone())),
        };
        assert_eq!(ctxt.generalize(mono), generalized);
    }
}
