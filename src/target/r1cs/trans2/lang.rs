//! IR -> Field lowering language

use std::cmp::Ord;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::hash::Hash;

use crate::ir::term::*;
use circ_fields::FieldT;
use rug::Integer;

/// The type of an encoding.
///
/// Encoding types should be ordered by cost. I.e. earlier types should be cheaper to produce. When
/// encodings of different types must be converted to a common type, all will be converted to the
/// cheapest.
pub trait EncodingType: Copy + Hash + Eq + Debug + Ord + 'static {
    /// Get the sort (pattern) for this encoding type.
    fn sort(&self) -> SortPattern;
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
    /// Output this encoding as a boolean term.
    fn as_bool_term(&self) -> Term;
    /// Convert this encoding to a new one of the same term.
    ///
    /// Will only be called with a type `to` whose sort agrees.
    ///
    /// Must return an encoding of the type `to`.
    fn convert(&self, c: &mut RewriteCtx, to: Self::Type) -> Self;
    /// Embed a variable.
    ///
    /// Must return an `e` such that `e.type_()` is equal to `ty`.
    fn variable(c: &mut RewriteCtx, name: &str, sort: &Sort, ty: Self::Type) -> Self;
    /// The above, but with the default encoding type.
    fn d_variable(c: &mut RewriteCtx, name: &str, sort: &Sort) -> Self {
        Self::variable(
            c,
            name,
            sort,
            <Self::Type as EncodingType>::default_for_sort(sort),
        )
    }
}

/// How inputs should be encoded for a [Rule].
pub enum EncTypes<T: EncodingType> {
    /// All encoded the same way.
    All(T),
    /// Encoded these ways.
    Seq(Vec<T>),
}

/// Chooses a rule for a term given the available encodings for the arguments.
pub(super) type Chooser<T> = Box<dyn Fn(&Term, &[&BTreeSet<T>]) -> usize>;

#[derive(Debug)]
/// The context in which a rewrite is performed
pub struct RewriteCtx {
    /// Assertions
    pub assertions: Vec<Term>,
    /// New variables that we introduce
    pub new_variables: Vec<(Term, String)>,
    field: FieldT,
    zero: Term,
    one: Term,
}

impl RewriteCtx {
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
    pub fn fresh(&mut self, ctx: &str, value: Term) -> Term {
        let i = self.new_variables.len();
        let name = format!("fresh_pf{}_{}", i, ctx);
        self.new_variables.push((value, name.clone()));
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
    // TODO: split zero, one, f_const into extension trait.
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
}

/// A rewrite rule for lowering IR to a finite-field assertion circuit.
pub struct Rule<E: Encoding> {
    /// Used to disabiguate rules that match the same term. Selectd by [Chooser] based on which
    /// input encodings are available.
    pub id: usize,
    pattern: Pattern,
    encoding_types: EncTypes<E::Type>,
    fn_: Box<dyn Fn(&mut RewriteCtx, &Op, &[&E]) -> E>,
}

impl<E: Encoding> Rule<E> {
    /// Create a new rule.
    pub(super) fn new<F: Fn(&mut RewriteCtx, &Op, &[&E]) -> E + 'static>(
        id: usize,
        op_pattern: OpPattern,
        sort: SortPattern,
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
    pub(super) fn apply(&self, c: &mut RewriteCtx, t: &Op, args: &[&E]) -> E {
        debug_assert_eq!(&OpPattern::from(t), &self.pattern.0);
        for (i, a) in args.iter().enumerate() {
            debug_assert_eq!(a.type_(), self.encoding_ty(i));
        }
        (self.fn_)(c, t, args)
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
/// A pattern for operators
pub enum OpPattern {
    /// Any constant.
    Const,
    /// See [Op::Eq].
    Eq,
    /// See [Op::Ite].
    Ite,
    /// See [Op::Not].
    Not,
    /// See [Op::Implies].
    Implies,
    /// See [Op::BoolMaj].
    BoolMaj,
    /// See [Op::BoolNaryOp].
    BoolNaryOp(BoolNaryOp),

    /// See [Op::BvBit].
    BvBit,

    /// See [Op::PfNaryOp].
    PfNaryOp(PfNaryOp),
    /// See [Op::PfUnOp].
    PfUnOp(PfUnOp),


    /// See [Op::BvBinOp].
    BvBinOp(BvBinOp),
    /// See [Op::BvBinPred].
    BvBinPred(BvBinPred),
    /// See [Op::BvNaryOp].
    BvNaryOp(BvNaryOp),
    /// See [Op::BvUnOp].
    BvUnOp(BvUnOp),
    /// See [Op::BoolToBv].
    BoolToBv,
    /// See [Op::BvExtract].
    BvExtract,
    /// See [Op::BvConcat].
    BvConcat,
    /// See [Op::BvUext].
    BvUext,
    /// See [Op::BvSext].
    BvSext,

    /// See [Op::PfToBv].
    PfToBv,
}

impl From<&Op> for OpPattern {
    fn from(op: &Op) -> Self {
        match op {
            Op::Const(..) => OpPattern::Const,
            Op::Eq => OpPattern::Eq,
            Op::Ite => OpPattern::Ite,
            Op::Not => OpPattern::Not,
            Op::BoolMaj => OpPattern::BoolMaj,
            Op::Implies => OpPattern::Implies,
            Op::BoolNaryOp(b) => OpPattern::BoolNaryOp(*b),
            Op::PfNaryOp(b) => OpPattern::PfNaryOp(*b),
            Op::PfUnOp(b) => OpPattern::PfUnOp(*b),
            Op::BvBit(_) => OpPattern::BvBit,
            Op::BvUnOp(b) => OpPattern::BvUnOp(*b),
            Op::BvNaryOp(b) => OpPattern::BvNaryOp(*b),
            Op::BvBinPred(b) => OpPattern::BvBinPred(*b),
            Op::BvBinOp(b) => OpPattern::BvBinOp(*b),
            Op::BvExtract(..) => OpPattern::BvExtract,
            Op::BvConcat => OpPattern::BvConcat,
            Op::BvUext(..) => OpPattern::BvUext,
            Op::BvSext(..) => OpPattern::BvSext,
            Op::PfToBv(..) => OpPattern::PfToBv,
            Op::BoolToBv => OpPattern::BoolToBv,
            _ => unimplemented!("op {}", op),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug)]
/// An abstraction of [Sort]
pub enum SortPattern {
    /// See [Sort::Bool]
    Bool,
    /// See [Sort::BitVector]
    BitVector,
    /// See [Sort::Field]
    Field,
}

impl From<&Sort> for SortPattern {
    fn from(s: &Sort) -> Self {
        match s {
            Sort::Bool => SortPattern::Bool,
            Sort::BitVector(_) => SortPattern::BitVector,
            Sort::Field(_) => SortPattern::Field,
            _ => unimplemented!("sort {}", s),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug, Copy)]
/// A pattern for sorted operators
pub struct Pattern(pub OpPattern, pub SortPattern);

impl<'a> From<&'a Term> for Pattern {
    fn from(t: &'a Term) -> Self {
        // get a term whose type is the parameter of this operator
        let term_of_type_param = match &t.op {
            Op::Ite => &t.cs[1],
            Op::Eq => &t.cs[0],
            Op::BvBit(_) => &t.cs[0],
            _ => t,
        };
        Pattern(
            OpPattern::from(&t.op),
            SortPattern::from(&check(term_of_type_param)),
        )
    }
}
