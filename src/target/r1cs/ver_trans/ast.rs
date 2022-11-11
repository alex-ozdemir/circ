//! Data-types used by the equiSAT rewriting language
//!
//! Comprises:
//! * [OpPattern]: expresses an *unindexed* operator (e.g. a constant without its value, or
//!   bit-vector signed extension without the number of added bits).
//! * [SortPattern]: expresses an *unindexed* sort (e.g., a bit-vector of unspecified width).
//! * [Pattern]: contains the two above.

use crate::ir::term::*;

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
    /// See [Op::UbvToPf].
    UbvToPf
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
            Op::UbvToPf(..) => OpPattern::UbvToPf,
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
