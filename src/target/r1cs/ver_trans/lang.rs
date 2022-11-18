//! IR -> Field lowering language

use std::cmp::Ord;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::hash::Hash;

use crate::ir::term::*;
use circ_fields::FieldT;
use rug::Integer;

pub use super::ast::{OpPat, Pattern, SortPat};

/// The type of an encoding.
///
/// Encoding types should be ordered by cost. I.e. earlier types should be cheaper to produce. When
/// encodings of different types must be converted to a common type, all will be converted to the
/// cheapest.
pub trait EncodingType: Copy + Hash + Eq + Debug + Ord + 'static {
    /// Get the sort (pattern) for this encoding type.
    fn sort(&self) -> SortPat;
    /// A list of all encoding types.
    fn all() -> Vec<Self>;
    /// Get the default type for a variable.
    fn default_for_sort(s: &Sort) -> Self;
}

/// The encoding itself.
pub trait Encoding: Clone + Debug {
    /// Types for this encoding.
    type Type: EncodingType;

    /// Get the type of this encoding.
    fn type_(&self) -> Self::Type;

    /// Assert this encoding equals another of the same type.
    fn assert_eq(&self, c: &mut Ctx, other: &Self);

    /// Convert this encoding to a new one of the same term.
    ///
    /// Will only be called with a type `to` whose sort agrees.
    ///
    /// Must return an encoding of the type `to`.
    fn convert(&self, c: &mut Ctx, to: Self::Type) -> Self;

    /// Embed a variable.
    ///
    /// Must return an `e` such that `e.type_()` is equal to `ty`.
    fn variable(c: &mut Ctx, name: &str, sort: &Sort, trust: bool) -> Self;

    /// Return the list of all rules applicable to this encoding.
    fn rules() -> Vec<Rule<Self>>;

    /// Choose a rule for this term given these available encodings.
    fn choose(t: &Term, available_encs: &[&BTreeSet<Self::Type>]) -> usize;

    /// [Enconding::const_], but with the default encoding type.
    fn const_(f: &FieldT, const_t: &Term) -> Self;

    /// Apply this function to all terms.
    fn map<F: Fn(Term) -> Term>(self, f: F) -> Self;
}

/// How inputs should be encoded for a [Rule].
pub enum EncTypes<T: EncodingType> {
    /// All encoded the same way.
    All(T),
    /// Encoded these ways.
    Seq(Vec<T>),
}

#[derive(Debug)]
/// The context in which a rewrite is performed
pub struct Ctx {
    /// Assertions
    pub assertions: Vec<Term>,
    /// New variables that we introduce (value, name, is_public).
    pub new_variables: Vec<(Term, String, bool)>,
    field: FieldT,
    zero: Term,
    one: Term,
}

impl Ctx {
    /// Create a new context
    pub fn new(field: FieldT) -> Self {
        Self {
            assertions: Vec::new(),
            zero: pf_lit(field.new_v(0)),
            one: pf_lit(field.new_v(1)),
            field,
            new_variables: Vec::new(),
        }
    }
    /// Given a value, construct a (fresh) variable meant to be set to this value and return it.
    ///
    /// The context is added to the variable name for debugging.
    pub fn fresh(&mut self, ctx: &str, value: Term, public: bool) -> Term {
        let i = self.new_variables.len();
        let name = format!("fresh_pf{}_{}", i, ctx);
        self.new_variables.push((value, name.clone(), public));
        leaf_term(Op::Var(name, Sort::Field(self.field.clone())))
    }
    /// add a new assertion
    pub fn assert(&mut self, t: Term) {
        self.assertions.push(t);
    }
    /// the field
    pub fn field(&self) -> &FieldT {
        &self.field
    }
    // TODO: split zero, one, f_const, assert_bit into extension trait.
    /// 0 in the field
    pub fn zero(&self) -> &Term {
        &self.zero
    }
    /// 1 in the field
    pub fn one(&self) -> &Term {
        &self.one
    }
    /// Create a new field constant
    pub fn f_const<I: Into<Integer>>(&self, i: I) -> Term {
        pf_lit(self.field().new_v(i.into()))
    }
    /// Bit-constraint
    pub fn assert_bit(&mut self, t: Term) {
        self.assert(term![EQ; term![PF_MUL; t.clone(), t.clone()], t.clone()]);
    }
}

/// A rewrite rule for lowering IR to a finite-field assertion circuit.
pub struct Rule<E: Encoding> {
    /// Used to disabiguate rules that match the same term. Selectd by [Chooser] based on which
    /// input encodings are available.
    pub id: usize,
    pattern: Pattern,
    encoding_types: EncTypes<E::Type>,
    fn_: Box<dyn Fn(&mut Ctx, &Op, &[&E]) -> E>,
}

impl<E: Encoding> Rule<E> {
    /// Create a new rule.
    pub(super) fn new<F: Fn(&mut Ctx, &Op, &[&E]) -> E + 'static>(
        id: usize,
        op_pattern: OpPat,
        sort: SortPat,
        encoding_types: EncTypes<E::Type>,
        f: F,
    ) -> Self {
        Self {
            id,
            pattern: Pattern(op_pattern, sort),
            encoding_types,
            fn_: Box::new(f),
        }
    }

    /// The pattern for this rule
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// The encoding for this rule's ith argument
    pub fn encoding_ty(&self, i: usize) -> E::Type {
        match &self.encoding_types {
            EncTypes::All(t) => *t,
            EncTypes::Seq(s) => {
                assert!(i < s.len());
                s[i]
            }
        }
    }

    /// Apply the rule
    pub(super) fn apply(&self, c: &mut Ctx, t: &Op, args: &[&E]) -> E {
        debug_assert_eq!(&OpPat::from(t), &self.pattern.0);
        for (i, a) in args.iter().enumerate() {
            debug_assert_eq!(a.type_(), self.encoding_ty(i));
        }
        (self.fn_)(c, t, args)
    }
}
