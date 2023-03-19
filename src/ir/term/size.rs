//! DataSize for our types.

use super::*;
use datasize::DataSize;
use std::mem::size_of;

impl DataSize for Sort {
    const IS_DYNAMIC: bool = true;

    const STATIC_HEAP_SIZE: usize = 0;

    fn estimate_heap_size(&self) -> usize {
        size_of::<Self>()
            + match self {
                Sort::BitVector(_)
                | Sort::F32
                | Sort::F64
                | Sort::Int
                | Sort::Field(_)
                | Sort::Bool => 0,
                Sort::Array(k, v, _) => k.estimate_heap_size() + v.estimate_heap_size(),
                Sort::Tuple(fs) => fs
                    .iter()
                    .map(|f| f.estimate_heap_size() + size_of::<Sort>())
                    .sum(),
            }
    }
}

pub use circ_fields::size::estimate_heap_size_integer;

impl DataSize for Value {
    const IS_DYNAMIC: bool = true;

    const STATIC_HEAP_SIZE: usize = 0;

    fn estimate_heap_size(&self) -> usize {
        match self {
            Value::F32(_) | Value::F64(_) | Value::Bool(_) => 0,
            Value::BitVector(x) => x.estimate_heap_size(),
            Value::Int(x) => estimate_heap_size_integer(x),
            Value::Field(x) => x.estimate_heap_size(),
            Value::Array(x) => x.estimate_heap_size(),
            Value::Tuple(x) => x
                .iter()
                .map(|i| i.estimate_heap_size() + size_of::<Value>())
                .sum(),
        }
    }
}

/// Ignore the size of this item
pub fn ignore<T>(_t: &T) -> usize {
    0
}

impl DataSize for Op {
    const IS_DYNAMIC: bool = true;
    const STATIC_HEAP_SIZE: usize = 0usize;
    #[inline]
    fn estimate_heap_size(&self) -> usize {
        match self {
            Op::Var(f0, f1) => DataSize::estimate_heap_size(f0) + DataSize::estimate_heap_size(f1),
            Op::Const(f0) => DataSize::estimate_heap_size(f0),
            Op::Ite => 0,
            Op::Eq => 0,
            Op::BvBinOp(f0) => DataSize::estimate_heap_size(f0),
            Op::BvBinPred(f0) => DataSize::estimate_heap_size(f0),
            Op::BvNaryOp(f0) => DataSize::estimate_heap_size(f0),
            Op::BvUnOp(f0) => DataSize::estimate_heap_size(f0),
            Op::BoolToBv => 0,
            Op::BvExtract(f0, f1) => {
                DataSize::estimate_heap_size(f0) + DataSize::estimate_heap_size(f1)
            }
            Op::BvConcat => 0,
            Op::BvUext(f0) => DataSize::estimate_heap_size(f0),
            Op::BvSext(f0) => DataSize::estimate_heap_size(f0),
            Op::PfToBv(f0) => DataSize::estimate_heap_size(f0),
            Op::Implies => 0,
            Op::BoolNaryOp(f0) => DataSize::estimate_heap_size(f0),
            Op::Not => 0,
            Op::BvBit(f0) => DataSize::estimate_heap_size(f0),
            Op::BoolMaj => 0,
            Op::FpBinOp(f0) => DataSize::estimate_heap_size(f0),
            Op::FpBinPred(f0) => DataSize::estimate_heap_size(f0),
            Op::FpUnPred(f0) => DataSize::estimate_heap_size(f0),
            Op::FpUnOp(f0) => DataSize::estimate_heap_size(f0),
            Op::BvToFp => 0,
            Op::UbvToFp(f0) => DataSize::estimate_heap_size(f0),
            Op::SbvToFp(f0) => DataSize::estimate_heap_size(f0),
            Op::FpToFp(f0) => DataSize::estimate_heap_size(f0),
            Op::PfUnOp(f0) => DataSize::estimate_heap_size(f0),
            Op::PfNaryOp(f0) => DataSize::estimate_heap_size(f0),
            Op::UbvToPf(f0) => DataSize::estimate_heap_size(f0),
            Op::PfChallenge(f0, f1) => {
                DataSize::estimate_heap_size(f0) + DataSize::estimate_heap_size(f1)
            }
            Op::PfFitsInBits(f0) => DataSize::estimate_heap_size(f0),
            Op::IntNaryOp(f0) => DataSize::estimate_heap_size(f0),
            Op::IntBinPred(f0) => DataSize::estimate_heap_size(f0),
            Op::Select => 0,
            Op::Store => 0,
            Op::CStore => 0,
            Op::Fill(f0, f1) => DataSize::estimate_heap_size(f0) + DataSize::estimate_heap_size(f1),
            Op::Array(f0, f1) => {
                DataSize::estimate_heap_size(f0) + DataSize::estimate_heap_size(f1)
            }
            Op::Tuple => 0,
            Op::Field(f0) => DataSize::estimate_heap_size(f0),
            Op::Update(f0) => DataSize::estimate_heap_size(f0),
            Op::Map(f0) => DataSize::estimate_heap_size(f0),
            Op::Call(f0, f1, f2) => {
                DataSize::estimate_heap_size(f0)
                    + DataSize::estimate_heap_size(f1)
                    + DataSize::estimate_heap_size(f2)
            }
            Op::Rot(f0) => DataSize::estimate_heap_size(f0),
            Op::PfToBoolTrusted => 0,
            Op::ExtOp(f0) => DataSize::estimate_heap_size(f0),
        }
    }
}
