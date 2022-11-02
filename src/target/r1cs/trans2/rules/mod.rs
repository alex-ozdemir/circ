//! Rules for lowering booleans and bit-vectors to a field

use super::lang::{Encoding, EncodingType, OpPattern, RewriteCtx, Rule, SortPattern};
use crate::ir::term::*;

use circ_fields::FieldT;
use rug::Integer;

use std::collections::BTreeSet;

pub mod ver;

/// Types of encodings
#[derive(Debug, Clone)]
pub enum Enc {
    /// A boolean {false, true} represented as {0, 1}.
    Bit(Term),
    /// A bit-vector as field-encoded bits.
    Bits(Vec<Term>),
    /// A bit-vector as a small field element.
    Uint(Term),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
/// Types of encodings, see [Enc].
pub enum Ty {
    /// See [Enc::Bit]
    Bit,
    /// See [Enc::Bits]
    Bits,
    /// See [Enc::Uint]
    Uint,
}

impl EncodingType for Ty {}

impl Enc {
    #[track_caller]
    pub(super) fn bit(&self) -> Term {
        match self {
            Enc::Bit(b) => b.clone(),
            _ => panic!("Tried to unwrap {:?} as a bit", self),
        }
    }
    #[track_caller]
    pub(super) fn bits(&self) -> &[Term] {
        match self {
            Enc::Bits(b) => b,
            _ => panic!("Tried to unwrap {:?} as bv bits", self),
        }
    }
    #[track_caller]
    #[allow(dead_code)]
    pub(super) fn uint(&self) -> Term {
        match self {
            Enc::Uint(b) => b.clone(),
            _ => panic!("Tried to unwrap {:?} as bv uint", self),
        }
    }
}

impl Encoding for Enc {
    type Type = Ty;
    fn type_(&self) -> Self::Type {
        match self {
            Enc::Bit(_) => Ty::Bit,
            Enc::Bits(_) => Ty::Bits,
            Enc::Uint(_) => Ty::Uint,
        }
    }

    fn as_bool_term(&self) -> Term {
        #[allow(irrefutable_let_patterns)]
        if let Enc::Bit(b) = self {
            term![EQ; b.clone(), pf_lit(FieldT::from(check(b).as_pf()).new_v(1))]
        } else {
            panic!("Cannot output encoding {:?}", self);
        }
    }

    fn variable(ctx: &mut RewriteCtx, name: &str, sort: &Sort) -> Self {
        match sort {
            Sort::Bool => {
                let t = leaf_term(Op::Var(name.into(), sort.clone()));
                let v = ctx.fresh(name, bool_to_field(t, ctx.field()));
                ctx.assert(term![EQ; term![PF_MUL; v.clone(), v.clone()], v.clone()]);
                Enc::Bit(v)
            }
            Sort::BitVector(w) => {
                let bv_t = leaf_term(Op::Var(name.into(), sort.clone()));
                Enc::Bits(
                    (0..*w)
                        .map(|i| {
                            let t = term![Op::BvBit(i); bv_t.clone()];
                            let v = ctx.fresh(name, bool_to_field(t, ctx.field()));
                            ctx.assert(term![EQ; term![PF_MUL; v.clone(), v.clone()], v.clone()]);
                            v
                        })
                        .collect(),
                )
            }
            s => unimplemented!("variable sort {}", s),
        }
    }
}

fn bool_neg(t: Term) -> Term {
    if let Sort::Field(f) = check(&t) {
        term![PF_ADD; pf_lit(f.new_v(1)), term![PF_NEG; t]]
    } else {
        panic!()
    }
}

fn bool_to_field(t: Term, f: &FieldT) -> Term {
    term![ITE; t, pf_lit(f.new_v(1)), pf_lit(f.new_v(0))]
}

fn rw_is_zero(ctx: &mut RewriteCtx, x: Term) -> Term {
    let eqz = term![Op::Eq; x.clone(), ctx.zero().clone()];
    // is_zero_inv * x == 1 - is_zero
    // is_zero * x == 0
    let m = ctx.fresh(
        "is_zero_inv",
        term![Op::Ite; eqz.clone(), ctx.zero().clone(), term![PF_RECIP; x.clone()]],
    );
    let is_zero = ctx.fresh("is_zero", bool_to_field(eqz, ctx.field()));
    ctx.assert(term![EQ; term![PF_MUL; m.clone(), x.clone()], bool_neg(is_zero.clone())]);
    ctx.assert(term![EQ; term![PF_MUL; is_zero.clone(), x], ctx.zero().clone()]);
    is_zero
}

fn rw_ensure_bit(ctx: &mut RewriteCtx, b: Term) {
    let b_minus_one = term![PF_ADD; b.clone(), term![PF_NEG; ctx.one().clone()]];
    ctx.assert(term![EQ; term![PF_MUL; b_minus_one, b], ctx.zero().clone()]);
}

fn rw_bit_split(ctx: &mut RewriteCtx, reason: &str, x: Term, n: usize) -> Vec<Term> {
    let x_bv = term![Op::PfToBv(n); x.clone()];
    let bits: Vec<Term> = (0..n)
        .map(|i| {
            ctx.fresh(
                // We get the right repr here because of infinite two's complement.
                &format!("{}_bit{}", reason, i),
                bool_to_field(term![Op::BvBit(i); x_bv.clone()], ctx.field()),
            )
        })
        .collect();
    let summands: Vec<Term> = bits
        .iter()
        .enumerate()
        .map(|(i, b)| {
            rw_ensure_bit(ctx, b.clone());
            term![PF_MUL; ctx.f_const(Integer::from(1) << i), b.clone()]
        })
        .collect();
    ctx.assert(term![EQ; term(PF_ADD, summands), x]);
    bits
}

fn rw_or_helper(ctx: &mut RewriteCtx, mut args: Vec<Term>) -> Term {
    loop {
        match args.len() {
            0 => return ctx.zero().clone(),
            1 => return args.pop().unwrap(),
            2 => {
                return bool_neg(
                    term![PF_MUL; bool_neg(args[0].clone()), bool_neg(args[1].clone())],
                )
            }
            i => {
                // assumes field is prime
                let take = if ctx.field().modulus() < &i {
                    ctx.field().modulus().to_usize().unwrap()
                } else {
                    i
                };
                let new = bool_neg(rw_is_zero(
                    ctx,
                    term(PF_ADD, args.drain(i - take..).collect()),
                ));

                args.push(new);
            }
        };
    }
}

fn rw_or(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(rw_or_helper(ctx, args.iter().map(|a| a.bit()).collect()))
}

fn rw_and(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(rw_or_helper(
        ctx,
        args.iter().map(|a| bool_neg(a.bit())).collect(),
    )))
}

fn rw_bool_eq(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(term![PF_ADD;
        ctx.one().clone(),
        term![PF_NEG; args[0].bit()],
        term![PF_NEG; args[1].bit()],
        term![PF_MUL; ctx.f_const(2), args[0].bit(), args[1].bit()]])
}

fn rw_xor(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    let mut args: Vec<Term> = args.iter().map(|a| a.bit()).collect();
    Enc::Bit(loop {
        match args.len() {
            0 => break ctx.zero().clone(),
            1 => break args.pop().unwrap(),
            2 => {
                break term![PF_ADD;
                    args[0].clone(),
                    args[1].clone(),
                    term![PF_NEG; term![PF_MUL; ctx.f_const(2), args[0].clone(), args[1].clone()]]]
            }
            i => {
                // assumes field is prime
                let take = if ctx.field().modulus() < &i {
                    ctx.field().modulus().to_usize().unwrap()
                } else {
                    i
                };
                let partial_sum = term(PF_ADD, args.drain(i - take..).collect());
                let num_bits = ((partial_sum.cs.len() as f64) + 0.2f64).log2() as usize + 1;
                let bits = rw_bit_split(ctx, "xor", partial_sum, num_bits);
                args.push(bits.into_iter().next().unwrap());
            }
        };
    })
}

fn rw_not(_ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(args[0].bit()))
}

fn rw_implies(_ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(
        term![PF_MUL; args[0].bit(), bool_neg(args[1].bit())],
    ))
}

fn rw_ite(_ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    let diff = term![PF_ADD; args[1].bit(), term![PF_NEG; args[2].bit()]];
    Enc::Bit(term![PF_ADD; term![PF_MUL; args[0].bit(), diff], args[2].bit()])
}

fn rw_const(ctx: &mut RewriteCtx, op: &Op, _args: &[&Enc]) -> Enc {
    if let Op::Const(Value::Bool(b)) = op {
        Enc::Bit(if *b {
            ctx.one().clone()
        } else {
            ctx.zero().clone()
        })
    } else {
        unreachable!()
    }
}

fn rw_maj(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    if let [a, b, c] = args {
        // m = ab + bc + ca - 2abc
        // m = ab + c(b + a - 2ab)
        let ab = term![PF_MUL; a.bit(), b.bit()];
        Enc::Bit(
            term![PF_ADD; ab.clone(), term![PF_MUL; c.bit(), term![PF_ADD; b.bit(), a.bit(), term![PF_MUL; ctx.f_const(-2), ab]]]],
        )
    } else {
        unreachable!()
    }
}

fn rw_bv_bit(_ctx: &mut RewriteCtx, op: &Op, args: &[&Enc]) -> Enc {
    if let Op::BvBit(i) = op {
        Enc::Bit(args[0].bits()[*i].clone())
    } else {
        unreachable!()
    }
}

fn rw_bv_const(ctx: &mut RewriteCtx, op: &Op, _args: &[&Enc]) -> Enc {
    if let Op::Const(Value::BitVector(bv)) = op {
        Enc::Bits(
            (0..bv.width())
                .map(|i| {
                    if bv.bit(i) {
                        ctx.one().clone()
                    } else {
                        ctx.zero().clone()
                    }
                })
                .collect(),
        )
    } else {
        unreachable!()
    }
}

/// The boolean/bv -> field rewrite rules.
pub fn rules() -> Vec<Rule<Enc>> {
    use OpPattern as OpP;
    use SortPattern::{BitVector, Bool};
    vec![
        Rule::new(OpP::Const, Bool, Ty::Bit, Box::new(rw_const)),
        Rule::new(OpP::Eq, Bool, Ty::Bit, Box::new(rw_bool_eq)),
        Rule::new(OpP::Ite, Bool, Ty::Bit, Box::new(rw_ite)),
        Rule::new(OpP::Not, Bool, Ty::Bit, Box::new(rw_not)),
        Rule::new(OpP::BoolMaj, Bool, Ty::Bit, Box::new(rw_maj)),
        Rule::new(OpP::Implies, Bool, Ty::Bit, Box::new(rw_implies)),
        Rule::new(
            OpP::BoolNaryOp(BoolNaryOp::Xor),
            Bool,
            Ty::Bit,
            Box::new(rw_xor),
        ),
        Rule::new(
            OpP::BoolNaryOp(BoolNaryOp::Or),
            Bool,
            Ty::Bit,
            Box::new(rw_or),
        ),
        Rule::new(
            OpP::BoolNaryOp(BoolNaryOp::And),
            Bool,
            Ty::Bit,
            Box::new(rw_and),
        ),
        Rule::new(OpP::Const, BitVector, Ty::Bits, Box::new(rw_bv_const)),
        Rule::new(OpP::BvBit, BitVector, Ty::Bits, Box::new(rw_bv_bit)),
    ]
}

/// Our encoding choice function
pub fn choose(t: &Term, _: &[&BTreeSet<Ty>]) -> Ty {
    match &t.op {
        Op::BoolMaj | Op::BoolNaryOp(_) | Op::Not | Op::Implies => Ty::Bit,
        Op::Eq => match check(&t.cs[0]) {
            Sort::Bool => Ty::Bit,
            Sort::BitVector(_) => Ty::Uint,
            _ => unimplemented!(),
        },
        Op::Const(Value::Bool(_)) => Ty::Bit,
        Op::Const(Value::BitVector(_)) => Ty::Bits,
        Op::BvBit(_) => Ty::Bits,
        _ => panic!(),
    }
}
