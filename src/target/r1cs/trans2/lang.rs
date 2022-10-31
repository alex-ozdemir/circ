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
pub trait EncodingType: Copy + Hash + Eq + Debug + Ord {}

/// The encoding itself.
pub trait Encoding: Clone {
    /// Types for this encoding.
    type Type: EncodingType;
    /// Get the type of this encoding.
    fn type_(&self) -> Self::Type;
    /// Output this encoding.
    fn output(&self, c: &mut RewriteCtx);
}

/// Chooses an encoding for a term given the available encodings for the arguments.
pub(super) type Chooser<T> = Box<dyn Fn(&Term, &[&BTreeSet<T>]) -> T>;

/// Encodes an input.
pub struct VarRule<E: Encoding> {
    sort_pattern: SortPattern,
    fn_: Box<dyn Fn(&mut RewriteCtx, &str, &Sort) -> E>,
}

impl<E: Encoding> VarRule<E> {
    pub(super) fn new<F: Fn(&mut RewriteCtx, &str, &Sort) -> E + 'static>(
        sort_pattern: SortPattern,
        f: F,
    ) -> Self {
        Self {
            sort_pattern,
            fn_: Box::new(f),
        }
    }

    /// Which sorts this rule matches
    pub fn sort_pattern(&self) -> SortPattern {
        self.sort_pattern
    }

    /// Apply the rule
    pub(super) fn apply(&self, c: &mut RewriteCtx, n: &str, s: &Sort) -> E {
        (self.fn_)(c, n, s)
    }

}

#[derive(Debug)]
#[allow(missing_docs)]
pub struct RewriteCtx {
    pub assertions: Vec<Term>,
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
    pattern: Pattern,
    encoding_type: E::Type,
    fn_: Box<dyn Fn(&mut RewriteCtx, &Op, &[&E]) -> E>,
}

/// A rewrite rule for lowering IR to a finite-field assertion circuit.
pub struct Conversion<E: Encoding> {
    from: E::Type,
    to: E::Type,
    fn_: Box<dyn Fn(&mut RewriteCtx, &E) -> E>,
}

impl<E: Encoding> Rule<E> {
    /// Create a new rule.
    pub(super) fn new<F: Fn(&mut RewriteCtx, &Op, &[&E]) -> E + 'static>(
        op_pattern: OpPattern,
        sort: SortPattern,
        encoding_type: E::Type,
        f: F,
    ) -> Self {
        Self {
            pattern: Pattern(op_pattern, sort),
            encoding_type,
            fn_: Box::new(f),
        }
    }

    /// The pattern for this rule
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// The encoding for this rule
    pub fn encoding_ty(&self) -> E::Type {
        self.encoding_type
    }

    /// Apply the rule
    pub(super) fn apply(&self, c: &mut RewriteCtx, t: &Op, args: &[&E]) -> E {
        debug_assert_eq!(&OpPattern::from(t), &self.pattern.0);
        for a in args {
            debug_assert_eq!(a.type_(), self.encoding_ty());
        }
        (self.fn_)(c, t, args)
    }
}

impl<E: Encoding> Conversion<E> {
    /// Create a new rule.
    #[allow(dead_code)]
    pub(super) fn new<F: Fn(&mut RewriteCtx, &E) -> E + 'static>(
        from: E::Type,
        to: E::Type,
        f: F,
    ) -> Self {
        Self {
            from,
            to,
            fn_: Box::new(f),
        }
    }

    /// The encoding this rule converts from
    pub fn from(&self) -> E::Type {
        self.from
    }

    /// The encoding this rule converts to
    pub fn to(&self) -> E::Type {
        self.to
    }

    /// Apply the rule
    pub(super) fn apply(&self, c: &mut RewriteCtx, e: &E) -> E {
        debug_assert_eq!(e.type_(), self.from());
        (self.fn_)(c, e)
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
/// A pattern for operators
pub enum OpPattern {
    /// Any constant.
    Const,
    /// See [Op::Eq].
    Eq,
    /// See [Op::Not].
    Not,
    /// See [Op::Implies].
    Implies,
    /// See [Op::BoolMaj].
    BoolMaj,
    /// See [Op::BoolNaryOp].
    BoolNaryOp(BoolNaryOp),
    /// See [Op::PfNaryOp].
    PfNaryOp(PfNaryOp),
    /// See [Op::PfUnOp].
    PfUnOp(PfUnOp),
}

impl From<&Op> for OpPattern {
    fn from(op: &Op) -> Self {
        match op {
            Op::Const(..) => OpPattern::Const,
            Op::Eq => OpPattern::Eq,
            Op::Not => OpPattern::Not,
            Op::BoolMaj => OpPattern::BoolMaj,
            Op::Implies => OpPattern::Implies,
            Op::BoolNaryOp(b) => OpPattern::BoolNaryOp(*b),
            Op::PfNaryOp(b) => OpPattern::PfNaryOp(*b),
            Op::PfUnOp(b) => OpPattern::PfUnOp(*b),
            _ => unimplemented!("op {}", op),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
/// An abstraction of [Sort]
pub enum SortPattern {
    /// See [Sort::Bool]
    Bool,
    /// See [Sort::BitVector]
    BitVector,
}

impl From<&Sort> for SortPattern {
    fn from(s: &Sort) -> Self {
        match s {
            Sort::Bool => SortPattern::Bool,
            Sort::BitVector(_) => SortPattern::BitVector,
            _ => unimplemented!("sort {}", s),
        }
    }
}

impl SortPattern {
    fn sorts(&self, bv_max_bits: usize) -> Vec<Sort> {
        match self {
            Self::BitVector => (1..=bv_max_bits).map(Sort::BitVector).collect(),
            Self::Bool => vec![Sort::Bool],
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug, Copy)]
/// A pattern for sorted operators
pub struct Pattern(pub OpPattern, pub SortPattern);

impl<'a> From<&'a Term> for Pattern {
    fn from(t: &'a Term) -> Self {
        Pattern(OpPattern::from(&t.op), SortPattern::from(&check(&t)))
    }
}

// TODO: split into extension trait.
impl Pattern {
    /// Get all operators that would match this pattern.
    ///
    /// Panics if there isn't a unique operator.
    pub fn get_ops(&self, bv_max_bits: usize) -> Vec<Op> {
        match self.0 {
            OpPattern::Const => {
                let iter = self.1.sorts(bv_max_bits).into_iter().flat_map(|s| {
                    let iter = s.elems_iter_values();
                    assert!(iter.size_hint().1.is_some(), "Infinite set");
                    iter
                });
                iter.map(Op::Const).collect()
            }
            OpPattern::Eq => vec![Op::Eq],
            OpPattern::Not => vec![Op::Not],
            OpPattern::BoolMaj => vec![Op::BoolMaj],
            OpPattern::Implies => vec![Op::Implies],
            OpPattern::BoolNaryOp(o) => vec![Op::BoolNaryOp(o)],
            OpPattern::PfUnOp(o) => vec![Op::PfUnOp(o)],
            OpPattern::PfNaryOp(o) => vec![Op::PfNaryOp(o)],
        }
    }
}
