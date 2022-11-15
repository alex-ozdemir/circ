//! Data-types used by the equiSAT rewriting language
//!
//! Comprises:
//! * [OpPat]: expresses an *unindexed* operator (e.g. a constant without its value, or
//!   bit-vector signed extension without the number of added bits).
//! * [SortPat]: expresses an *unindexed* sort (e.g., a bit-vector of unspecified width).
//! * [Pattern]: contains the two above.

use crate::ir::term::*;

use std::fmt::{self, Display, Formatter};

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
/// A pattern for operators
pub enum OpPat {
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

impl Display for OpPat {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            OpPat::Ite => write!(f, "ite"),
            OpPat::Eq => write!(f, "="),
            OpPat::BvBinOp(a) => write!(f, "{}", a),
            OpPat::BvBinPred(a) => write!(f, "{}", a),
            OpPat::BvNaryOp(a) => write!(f, "{}", a),
            OpPat::BvUnOp(a) => write!(f, "{}", a),
            OpPat::BoolToBv => write!(f, "bool2bv"),
            OpPat::BvExtract => write!(f, "extract"),
            OpPat::BvConcat => write!(f, "concat"),
            OpPat::BvUext => write!(f, "uext"),
            OpPat::BvSext => write!(f, "sext"),
            OpPat::PfToBv => write!(f, "pf2bv"),
            OpPat::Implies => write!(f, "=>"),
            OpPat::BoolNaryOp(a) => write!(f, "{}", a),
            OpPat::Not => write!(f, "not"),
            OpPat::BvBit => write!(f, "bit"),
            OpPat::BoolMaj => write!(f, "maj"),
            OpPat::PfUnOp(a) => write!(f, "{}", a),
            OpPat::PfNaryOp(a) => write!(f, "{}", a),
            OpPat::UbvToPf => write!(f, "ubv2pf"),
        }
    }
}

impl From<&Op> for OpPat {
    fn from(op: &Op) -> Self {
        match op {
            Op::Eq => OpPat::Eq,
            Op::Ite => OpPat::Ite,
            Op::Not => OpPat::Not,
            Op::BoolMaj => OpPat::BoolMaj,
            Op::Implies => OpPat::Implies,
            Op::BoolNaryOp(b) => OpPat::BoolNaryOp(*b),
            Op::PfNaryOp(b) => OpPat::PfNaryOp(*b),
            Op::PfUnOp(b) => OpPat::PfUnOp(*b),
            Op::BvBit(_) => OpPat::BvBit,
            Op::BvUnOp(b) => OpPat::BvUnOp(*b),
            Op::BvNaryOp(b) => OpPat::BvNaryOp(*b),
            Op::BvBinPred(b) => OpPat::BvBinPred(*b),
            Op::BvBinOp(b) => OpPat::BvBinOp(*b),
            Op::BvExtract(..) => OpPat::BvExtract,
            Op::BvConcat => OpPat::BvConcat,
            Op::BvUext(..) => OpPat::BvUext,
            Op::BvSext(..) => OpPat::BvSext,
            Op::PfToBv(..) => OpPat::PfToBv,
            Op::BoolToBv => OpPat::BoolToBv,
            Op::UbvToPf(..) => OpPat::UbvToPf,
            _ => unimplemented!("op {}", op),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug)]
/// An abstraction of [Sort]
pub enum SortPat {
    /// See [Sort::Bool]
    Bool,
    /// See [Sort::BitVector]
    BitVector,
    /// See [Sort::Field]
    Field,
}

impl From<&Sort> for SortPat {
    fn from(s: &Sort) -> Self {
        match s {
            Sort::Bool => SortPat::Bool,
            Sort::BitVector(_) => SortPat::BitVector,
            Sort::Field(_) => SortPat::Field,
            _ => unimplemented!("sort {}", s),
        }
    }
}

impl Display for SortPat {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            SortPat::Bool => write!(f, "bool"),
            SortPat::BitVector => write!(f, "bv"),
            SortPat::Field => write!(f, "field"),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug, Copy)]
/// A pattern for sorted operators
pub struct Pattern(pub OpPat, pub SortPat);

impl<'a> From<&'a Term> for Pattern {
    fn from(t: &'a Term) -> Self {
        // get a term whose type is the parameter of this operator
        let term_of_type_param = match &t.op {
            Op::Ite => &t.cs[1],
            Op::Eq => &t.cs[0],
            Op::BvBit(_) => &t.cs[0],
            Op::BvBinPred(_) => &t.cs[0],
            _ => t,
        };
        Pattern(
            OpPat::from(&t.op),
            SortPat::from(&check(term_of_type_param)),
        )
    }
}
