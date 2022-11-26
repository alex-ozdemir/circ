//! Verification shim for our rules.

use super::super::ver::VerifiableEncoding;
use super::{Enc, Ty};
use crate::ir::term::*;

use circ_fields::FieldT;

use rug::Integer;

fn bitsum(f: &FieldT, bits: impl Iterator<Item = Term>) -> Term {
    let mut s = Integer::from(1);
    let mut summands: Vec<Term> = Vec::new();
    for b in bits {
        let t = term![PF_MUL; pf_lit(f.new_v(&s)), b];
        s <<= 1;
        summands.push(t);
    }
    term(PF_ADD, summands)
}

fn bv_to_bits(bv: Term) -> impl Iterator<Item = Term> {
    let w = check(&bv).as_bv();
    (0..w).map(move |i| term![Op::BvBit(i); bv.clone()])
}

fn bool_to_pf(b: Term, f: &FieldT) -> Term {
    let (zero, one) = (pf_lit(f.new_v(0)), pf_lit(f.new_v(1)));
    term![ITE; b, one, zero]
}

fn bv_to_pf_bits(bv: Term, f: FieldT) -> impl Iterator<Item = Term> {
    bv_to_bits(bv).map(move |b| bool_to_pf(b, &f))
}

fn fresh(f: &FieldT, n: String) -> Term {
    leaf_term(Op::Var(n, Sort::Field(f.clone())))
}

impl VerifiableEncoding for Enc {
    fn floating(prefix: &str, ty: Self::Type, f: &FieldT, s: &Sort) -> Self {
        match ty {
            Ty::Bit => Enc::Bit(fresh(f, format!("{}_bit", prefix))),
            Ty::Bits => Enc::Bits(
                (0..s.as_bv())
                    .map(|i| fresh(f, format!("{}_bit{}", prefix, i)))
                    .collect(),
            ),
            Ty::Uint => Enc::Uint(fresh(f, format!("{}_uint", prefix)), s.as_bv()),
            Ty::Field => Enc::Field(fresh(f, format!("{}_f", prefix))),
        }
    }

    fn is_valid(&self, t: Term) -> Term {
        let field = self.f();
        match self {
            Enc::Bit(f) => {
                let f_valid = term![EQ; term![PF_MUL; f.clone(), f.clone()], f.clone()];
                term![AND; f_valid, term![EQ; self.to_term(), t]]
            }
            Enc::Bits(fs) => term(
                AND,
                bv_to_pf_bits(t, field)
                    .zip(fs)
                    .map(|(a, b)| term![EQ; a, b.clone()])
                    .collect(),
            ),
            Enc::Uint(f, _) => {
                term![EQ; bitsum(&field, bv_to_pf_bits(t, field.clone())), f.clone()]
            }
            Enc::Field(f) => term![EQ; f.clone(), t],
        }
    }

    fn from_term(t: Term, ty: Self::Type, f: &FieldT) -> Self {
        match ty {
            Ty::Bit => Enc::Bit(bool_to_pf(t, f)),
            Ty::Bits => Enc::Bits(bv_to_pf_bits(t, f.clone()).collect()),
            Ty::Uint => Enc::Uint(term![Op::UbvToPf(f.clone()); t.clone()], check(&t).as_bv()),
            Ty::Field => Enc::Field(t),
        }
    }

    fn to_term(&self) -> Term {
        match self {
            Enc::Bit(b) => term![EQ; pf_lit(self.f().new_v(1)), b.clone()],
            Enc::Bits(bs) => term![Op::PfToBv(bs.len()); bitsum(&self.f(), bs.clone().into_iter())],
            Enc::Uint(u, w) => term![Op::PfToBv(*w); u.clone()],
            Enc::Field(f) => f.clone(),
        }
    }
}
