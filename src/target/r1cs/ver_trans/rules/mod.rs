//! Rules for lowering booleans and bit-vectors to a field

use super::lang::{EncTypes, Encoding, EncodingType, OpPat, Ctx, Rule, SortPat};
use crate::ir::term::*;
use crate::target::bitsize;

use circ_fields::FieldT;
use rug::{ops::Pow, Integer};

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
    Uint(Term, usize),
    /// A prime field element.
    Field(Term),
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
    /// See [Enc::Field]
    Field,
}

impl EncodingType for Ty {
    fn sort(&self) -> SortPat {
        match self {
            Ty::Bit => SortPat::Bool,
            Ty::Bits => SortPat::BitVector,
            Ty::Uint => SortPat::BitVector,
            Ty::Field => SortPat::Field,
        }
    }

    fn all() -> Vec<Self> {
        vec![Self::Bit, Self::Bits, Self::Uint, Self::Field]
    }

    fn default_for_sort(s: &Sort) -> Self {
        match s {
            Sort::Bool => Ty::Bit,
            Sort::Field(_) => Ty::Field,
            Sort::BitVector(_) => Ty::Bits,
            _ => unimplemented!(),
        }
    }
}

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
    pub(super) fn uint(&self) -> (Term, usize) {
        match self {
            Enc::Uint(b, u) => (b.clone(), *u),
            _ => panic!("Tried to unwrap {:?} as bv uint", self),
        }
    }
    #[track_caller]
    pub(super) fn field(&self) -> Term {
        match self {
            Enc::Field(f) => f.clone(),
            _ => panic!("Tried to unwrap {:?} as field value", self),
        }
    }
    #[track_caller]
    pub(super) fn w(&self) -> usize {
        match self {
            Enc::Uint(_, u) => *u,
            Enc::Bits(bs) => bs.len(),
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
            Enc::Uint(_, _) => Ty::Uint,
            Enc::Field(_) => Ty::Field,
        }
    }

    fn as_bool_term(&self) -> Term {
        if let Enc::Bit(b) = self {
            term![EQ; b.clone(), pf_lit(FieldT::from(check(b).as_pf()).new_v(1))]
        } else {
            panic!("Cannot output encoding {:?}", self);
        }
    }

    fn variable(ctx: &mut Ctx, name: &str, sort: &Sort, ty: Ty) -> Self {
        assert_eq!(SortPat::from(sort), ty.sort());
        let t = leaf_term(Op::Var(name.into(), sort.clone()));
        match ty {
            Ty::Bit => {
                let v = ctx.fresh(name, bool_to_field(t, ctx.field()));
                ctx.assert(term![EQ; term![PF_MUL; v.clone(), v.clone()], v.clone()]);
                Enc::Bit(v)
            }
            Ty::Bits => {
                let w = sort.as_bv();
                Enc::Bits(
                    (0..w)
                        .map(|i| {
                            let bit_t = term![Op::BvBit(i); t.clone()];
                            let v = ctx.fresh(name, bool_to_field(bit_t, ctx.field()));
                            ctx.assert(term![EQ; term![PF_MUL; v.clone(), v.clone()], v.clone()]);
                            v
                        })
                        .collect(),
                )
            }
            Ty::Uint => {
                let w = sort.as_bv();
                let bits: Vec<Term> = (0..w)
                    .map(|i| {
                        let bit_t = term![Op::BvBit(i); t.clone()];
                        let v = ctx.fresh(name, bool_to_field(bit_t, ctx.field()));
                        ctx.assert(term![EQ; term![PF_MUL; v.clone(), v.clone()], v.clone()]);
                        v
                    })
                    .collect();
                let sum = term(PF_ADD, bits.iter().enumerate().map(|(i, f)|
                        term![PF_MUL; pf_lit(ctx.field().new_v(Integer::from(1) << i)), f.clone()]).collect());
                Enc::Uint(sum, w)
            }
            Ty::Field => Enc::Field(ctx.fresh(name, t)),
        }
    }

    fn convert(&self, ctx: &mut Ctx, to: Self::Type) -> Self {
        match (self, to) {
            (Self::Bits(bs), Ty::Uint) => {
                let field = FieldT::from(check(&bs[0]).as_pf());
                Enc::Uint(term(
                    PF_ADD,
                    bs.iter()
                        .enumerate()
                        .map(|(i, f)| term![PF_MUL; pf_lit(field.new_v(Integer::from(1) << i)), f.clone()])
                        .collect(),
                ), bs.len())
            }
            (Self::Uint(t, w), Ty::Bits) => {
                let bv_t = term![Op::PfToBv(*w); t.clone()];
                let bits: Vec<Term> = (0..*w)
                    .map(|i| {
                        let bit_t = term![Op::BvBit(i); bv_t.clone()];
                        let v =
                            ctx.fresh(&format!("conv_bit{}", i), bool_to_field(bit_t, ctx.field()));
                        ctx.assert(term![EQ; term![PF_MUL; v.clone(), v.clone()], v.clone()]);
                        v
                    })
                    .collect();
                let field = FieldT::from(check(&t).as_pf());
                let sum = term(
                    PF_ADD,
                    bits.iter()
                        .enumerate()
                        .map(|(i, f)| term![PF_MUL; pf_lit(field.new_v(Integer::from(1) << i)), f.clone()])
                        .collect(),
                );
                ctx.assert(term![EQ; sum, t.clone()]);
                Enc::Bits(bits)
            }
            (Self::Bits(_), Ty::Bits) => self.clone(),
            (Self::Uint(_, _), Ty::Uint) => self.clone(),
            (Self::Bit(_), Ty::Bit) => self.clone(),
            (Self::Field(_), Ty::Field) => self.clone(),
            _ => unimplemented!("invalid conversion"),
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

fn is_zero(ctx: &mut Ctx, x: Term) -> Term {
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

fn ensure_bit(ctx: &mut Ctx, b: Term) {
    let b_minus_one = term![PF_ADD; b.clone(), term![PF_NEG; ctx.one().clone()]];
    ctx.assert(term![EQ; term![PF_MUL; b_minus_one, b], ctx.zero().clone()]);
}

fn bit_split(ctx: &mut Ctx, reason: &str, x: Term, n: usize) -> Vec<Term> {
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
            ensure_bit(ctx, b.clone());
            term![PF_MUL; ctx.f_const(Integer::from(1) << i), b.clone()]
        })
        .collect();
    ctx.assert(term![EQ; term(PF_ADD, summands), x]);
    bits
}

fn bit_join(f: &FieldT, bits: impl Iterator<Item = Term>) -> Term {
    let mut s = Integer::from(1);
    let summands: Vec<Term> = bits
        .map(|b| {
            let t = term![PF_MUL; pf_lit(f.new_v(&s)), b];
            s <<= 1;
            t
        })
        .collect();
    term(PF_ADD, summands)
}

#[allow(dead_code)]
fn sign_bit_join(f: &FieldT, bits: &[Term]) -> Term {
    let mut s = Integer::from(1);
    let summands: Vec<Term> = bits
        .iter()
        .take(bits.len() - 1)
        .map(|b| {
            let t = term![PF_MUL; pf_lit(f.new_v(&s)), b.clone()];
            s <<= 1;
            t
        })
        .chain(std::iter::once(term![PF_MUL; pf_lit(f.new_v(&-(Integer::from(1) << bits.len()))), bits.last().unwrap().clone()]))
        .collect();
    term(PF_ADD, summands)
}

fn or_helper(ctx: &mut Ctx, mut args: Vec<Term>) -> Term {
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
                let new = bool_neg(is_zero(ctx, term(PF_ADD, args.drain(i - take..).collect())));

                args.push(new);
            }
        };
    }
}

fn or(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(or_helper(ctx, args.iter().map(|a| a.bit()).collect()))
}

fn and(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(or_helper(
        ctx,
        args.iter().map(|a| bool_neg(a.bit())).collect(),
    )))
}

fn bool_eq(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(term![PF_ADD;
        ctx.one().clone(),
        term![PF_NEG; args[0].bit()],
        term![PF_NEG; args[1].bit()],
        term![PF_MUL; ctx.f_const(2), args[0].bit(), args[1].bit()]])
}

fn xor(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(xor_helper(ctx, args.iter().map(|a| a.bit()).collect()))
}

fn xor_helper(ctx: &mut Ctx, mut args: Vec<Term>) -> Term {
    loop {
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
                let bits = bit_split(ctx, "xor", partial_sum, num_bits);
                args.push(bits.into_iter().next().unwrap());
            }
        };
    }
}

fn not(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(args[0].bit()))
}

fn implies(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(
        term![PF_MUL; args[0].bit(), bool_neg(args[1].bit())],
    ))
}

fn ite(c: Term, t: Term, f: Term) -> Term {
    term![PF_ADD; term![PF_MUL; c, term![PF_ADD; t, term![PF_NEG; f.clone()]]], f]
}

fn bool_ite(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(ite(args[0].bit(), args[1].bit(), args[2].bit()))
}

fn bool_const(ctx: &mut Ctx, op: &Op, _args: &[&Enc]) -> Enc {
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

fn maj(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
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

fn bv_bit(_ctx: &mut Ctx, op: &Op, args: &[&Enc]) -> Enc {
    if let Op::BvBit(i) = op {
        Enc::Bit(args[0].bits()[*i].clone())
    } else {
        unreachable!()
    }
}

fn bv_const(ctx: &mut Ctx, op: &Op, _args: &[&Enc]) -> Enc {
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

fn bv_ite(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Uint(
        ite(args[0].bit(), args[1].uint().0, args[2].uint().0),
        args[1].w(),
    )
}

fn bv_not(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bits(args[0].bits().iter().map(|b| bool_neg(b.clone())).collect())
}

fn bv_neg(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    let (x, w) = args[0].uint();
    let field = FieldT::from(check(&x).as_pf());
    let zero = is_zero(ctx, x.clone());
    let diff = term![PF_ADD; pf_lit(field.new_v(Integer::from(1) << w)), term![PF_NEG; x]];
    Enc::Uint(ite(zero, pf_lit(field.new_v(0)), diff), w)
}

fn bv_eq(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(is_zero(
        ctx,
        term![PF_ADD; args[0].uint().0, term![PF_NEG; args[1].uint().0]],
    ))
}

fn bv_uext_bits(ctx: &mut Ctx, op: &Op, args: &[&Enc]) -> Enc {
    match op {
        Op::BvUext(n) => Enc::Bits(
            args[0]
                .bits()
                .into_iter()
                .cloned()
                .chain(std::iter::repeat(ctx.zero().clone()).take(*n))
                .collect(),
        ),
        _ => panic!(),
    }
}

fn bv_uext_uint(_ctx: &mut Ctx, op: &Op, args: &[&Enc]) -> Enc {
    if let Op::BvUext(n) = op {
        let (x, w) = args[0].uint();
        Enc::Uint(x, w + *n)
    } else {
        panic!()
    }
}

fn bv_sext(_ctx: &mut Ctx, op: &Op, args: &[&Enc]) -> Enc {
    match op {
        Op::BvSext(n) => Enc::Bits({
            let mut bits = args[0].bits().into_iter().rev();
            let ext_bits = std::iter::repeat(bits.next().expect("sign ext empty")).take(n + 1);
            bits.rev().chain(ext_bits).cloned().collect()
        }),
        _ => panic!(),
    }
}

fn bool_to_bv(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bits(vec![args[0].bit()])
}

fn transpose_bits(args: &[&Enc]) -> Vec<Vec<Term>> {
    let mut bits = vec![vec![]; args[0].bits().len()];
    for a in args {
        for (i, b) in a.bits().iter().enumerate() {
            bits[i].push(b.clone());
        }
    }
    bits
}

fn bv_and(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bits(
        transpose_bits(args)
            .into_iter()
            .map(|bs| bool_neg(or_helper(ctx, bs.into_iter().map(bool_neg).collect())))
            .collect(),
    )
}

fn bv_or(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bits(
        transpose_bits(args)
            .into_iter()
            .map(|bs| or_helper(ctx, bs))
            .collect(),
    )
}

fn bv_xor(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bits(
        transpose_bits(args)
            .into_iter()
            .map(|bs| xor_helper(ctx, bs))
            .collect(),
    )
}

fn pf_to_bv(ctx: &mut Ctx, op: &Op, args: &[&Enc]) -> Enc {
    match op {
        Op::PfToBv(w) => Enc::Bits(bit_split(ctx, "pf_to_field", args[0].field(), *w)),
        _ => unreachable!(),
    }
}

fn pf_add(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Field(term(PF_ADD, args.into_iter().map(|a| a.field()).collect()))
}

fn pf_mul(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Field(term(PF_MUL, args.into_iter().map(|a| a.field()).collect()))
}

fn pf_neg(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Field(term![PF_NEG; args[0].field()])
}

fn pf_ite(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Field(ite(args[0].bit(), args[1].field(), args[2].field()))
}

#[allow(dead_code)]
fn ubv_to_pf(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Field(args[0].uint().0)
}

fn pf_recip(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    // Used to enforce ix = 1 (incomplete on x = 0)
    // Now we enforce:
    // xi = 1 - z
    // xz = 0
    // iz = 0
    let x = args[0].field();
    let eqz = term![Op::Eq; x.clone(), ctx.zero().clone()];
    let z = ctx.fresh("recip_z", bool_to_field(eqz, ctx.field()));
    let i = ctx.fresh("recip_i", term![PF_RECIP; args[0].field()]);
    ctx.assert(term![EQ; term![PF_MUL; x.clone(), i.clone()], bool_neg(z.clone())]);
    ctx.assert(term![EQ; term![PF_MUL; x.clone(), z.clone()], ctx.zero().clone()]);
    ctx.assert(term![EQ; term![PF_MUL; i.clone(), z.clone()], ctx.zero().clone()]);
    Enc::Field(i)
}

#[allow(dead_code)]
fn pf_const(ctx: &mut Ctx, op: &Op, _args: &[&Enc]) -> Enc {
    if let Op::Const(Value::Field(b)) = op {
        Enc::Field(ctx.f_const(b))
    } else {
        unreachable!()
    }
}

fn bv_add(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    let w = args[0].w();
    let extra_width = bitsize(args.len().saturating_sub(1));
    let sum = term(PF_ADD, args.iter().map(|a| a.uint().0).collect());
    Enc::Bits(
        bit_split(ctx, "sum", sum, w + extra_width)
            .into_iter()
            .take(w)
            .collect(),
    )
}

fn bv_mul(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    let w = args[0].w();
    let f_width = ctx.field().modulus().significant_bits() as usize - 1;
    let (to_split, split_w) = if args.len() * w < f_width {
        (
            term(PF_MUL, args.iter().map(|a| a.uint().0).collect()),
            args.len() * w,
        )
    } else {
        let p = args.iter().fold(ctx.one().clone(), |acc, v| {
            let p = term![PF_MUL; acc, v.uint().0];
            let mut bits = bit_split(ctx, "binMul", p, 2 * w);
            bits.truncate(w);
            bit_join(ctx.field(), bits.iter().cloned())
        });
        (p, w)
    };
    let mut bs = bit_split(ctx, "sum", to_split, split_w);
    bs.truncate(w);
    Enc::Bits(bs)
}

fn bv_extract(_ctx: &mut Ctx, op: &Op, args: &[&Enc]) -> Enc {
    if let Op::BvExtract(high, low) = op {
        Enc::Bits(
            args[0]
                .bits()
                .into_iter()
                .skip(*low)
                .take(*high - *low + 1)
                .cloned()
                .collect(),
        )
    } else {
        unreachable!()
    }
}

fn bv_concat(_ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    let mut bits = Vec::new();
    for a in args.iter().rev() {
        bits.extend(a.bits().into_iter().cloned())
    }
    Enc::Bits(bits)
}

fn bv_sub(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    let (a, n) = args[0].uint();
    let sum = term![PF_ADD; a, ctx.f_const(Integer::from(2).pow(n as u32)), term![PF_NEG; args[1].uint().0]];
    let mut bits = bit_split(ctx, "sub", sum, n + 1);
    bits.truncate(n);
    Enc::Bits(bits)
}

fn fits_in_bits(ctx: &mut Ctx, reason: &str, x: Term, n: usize) -> Term {
    let bits = bit_split(ctx, &format!("{}_fit", reason), x.clone(), n);
    let sum = bit_join(ctx.field(), bits.into_iter());
    is_zero(ctx, term![PF_ADD; sum, term![PF_NEG; x]])
}

fn bv_ge(ctx: &mut Ctx, a: Term, b: Term, n: usize) -> Term {
    fits_in_bits(ctx, "ge", term![PF_ADD; a, term![PF_NEG; b]], n)
}

fn sub_one(x: Term) -> Term {
    let neg_one = pf_lit(FieldT::from(check(&x).as_pf()).new_v(-1));
    term![PF_ADD; x, neg_one]
}

fn bv_uge(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bv_ge(ctx, args[0].uint().0, args[1].uint().0, args[0].w()))
}

fn bv_ugt(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bv_ge(
        ctx,
        sub_one(args[0].uint().0),
        args[1].uint().0,
        args[0].w(),
    ))
}

fn bv_ule(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bv_ge(ctx, args[1].uint().0, args[0].uint().0, args[0].w()))
}

fn bv_ult(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bv_ge(
        ctx,
        sub_one(sign_bit_join(ctx.field(), args[1].bits())),
        sign_bit_join(ctx.field(), args[0].bits()),
        args[0].w(),
    ))
}

fn bv_sge(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bv_ge(
        ctx,
        sign_bit_join(ctx.field(), args[0].bits()),
        sign_bit_join(ctx.field(), args[1].bits()),
        args[0].bits().len(),
    ))
}

fn bv_sgt(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bv_ge(
        ctx,
        sub_one(sign_bit_join(ctx.field(), args[0].bits())),
        sign_bit_join(ctx.field(), args[1].bits()),
        args[0].bits().len(),
    ))
}

fn bv_sle(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bv_ge(
        ctx,
        sign_bit_join(ctx.field(), args[1].bits()),
        sign_bit_join(ctx.field(), args[0].bits()),
        args[0].bits().len(),
    ))
}

fn bv_slt(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bv_ge(
        ctx,
        sub_one(sign_bit_join(ctx.field(), args[1].bits())),
        sign_bit_join(ctx.field(), args[0].bits()),
        args[0].bits().len(),
    ))
}

// returns the bits of q and r such that a = qb + r
// with 0 <= r < b
//
// if b = 0, TODO
fn ubv_qr(ctx: &mut Ctx, a: Term, b: Term, n: usize) -> (Vec<Term>, Vec<Term>) {
    let is_zero = is_zero(ctx, b.clone());
    let a_bv_term = term![Op::PfToBv(n); a.clone()];
    let b_bv_term = term![Op::PfToBv(n); b.clone()];
    let q_term = term![Op::UbvToPf(ctx.field().clone()); term![BV_UDIV; a_bv_term.clone(), b_bv_term.clone()]];
    let r_term = term![Op::UbvToPf(ctx.field().clone()); term![BV_UREM; a_bv_term, b_bv_term]];
    let q = ctx.fresh("div_q", q_term);
    let r = ctx.fresh("div_r", r_term);
    let qb = bit_split(ctx, "div_q", q.clone(), n);
    let rb = bit_split(ctx, "div_r", r.clone(), n);
    ctx.assert(term![EQ; term![PF_MUL; q.clone(), b.clone()],
    term![PF_ADD; a, term![PF_NEG; r.clone()]]]);
    let is_gt = bv_ge(
        ctx,
        term![PF_ADD; b, term![PF_NEG; ctx.one().clone()]],
        r,
        n,
    );
    let is_not_ge = bool_neg(is_gt);
    let is_not_zero = bool_neg(is_zero);
    ctx.assert(term![EQ; term![PF_MUL; is_not_ge, is_not_zero], ctx.zero().clone()]);
    (qb, rb)
}

fn bv_udiv(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bits(ubv_qr(ctx, args[0].uint().0, args[1].uint().0, args[0].w()).0)
}

fn bv_urem(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bits(ubv_qr(ctx, args[0].uint().0, args[1].uint().0, args[0].w()).1)
}

/// Shift `x` left by `2^y`, if bit-valued `c` is true.
fn const_pow_shift_bv(ctx: &mut Ctx, x: Term, y: usize, c: Term) -> Term {
    ite(c, term![PF_MUL; x.clone(), ctx.f_const(1 << (1 << y))], x)
}

/// Shift `x` left by `y`, filling the blank spots with bit-valued `ext_bit`.
/// Returns an *oversized* number
fn shift_bv(ctx: &mut Ctx, x: Term, y: Vec<Term>, ext_bit: Option<Term>) -> Term {
    if let Some(b) = ext_bit {
        let left = shift_bv(ctx, x, y.clone(), None);
        let right = sub_one(shift_bv(ctx, b.clone(), y, None));
        term![PF_ADD; left, term![PF_MUL; b, right]]
    } else {
        y.into_iter()
            .enumerate()
            .fold(x, |x, (i, yi)| const_pow_shift_bv(ctx, x, i, yi))
    }
}

/// Shift `x` left by `y`, filling the blank spots with bit-valued `ext_bit`.
/// Returns a bit sequence.
///
/// If `c` is true, returns bit sequence which is just a copy of `ext_bit`.
fn shift_bv_bits(
    ctx: &mut Ctx,
    x: Term,
    y: Vec<Term>,
    ext_bit: Option<Term>,
    x_w: usize,
    c: Term,
) -> Vec<Term> {
    let y_w = y.len();
    let mask = match ext_bit.as_ref() {
        Some(e) => term![PF_MUL; e.clone(), ctx.f_const((1 << x_w) - 1)],
        None => ctx.zero().clone(),
    };
    let s = shift_bv(ctx, x, y, ext_bit);
    let masked_s = ite(c, mask, s);
    let mut bits = bit_split(ctx, "shift", masked_s, (1 << y_w) + x_w - 1);
    bits.truncate(x_w);
    bits
}

/// Given a shift amount expressed as a bit-sequence, splits that shift into low bits and high
/// bits. The number of low bits, `b`, is the minimum amount such that `data_w-1` is representable
/// in `b` bits. The rest of the bits (the high ones) are or'd together into a single bit that is
/// returned.
fn split_shift_amt(
    ctx: &mut Ctx,
    data_w: usize,
    mut shift_amt: Vec<Term>,
) -> (Term, Vec<Term>) {
    let b = bitsize(data_w - 1);
    let some_high_bit = or_helper(ctx, shift_amt.drain(b..).collect());
    (some_high_bit, shift_amt)
}

fn bv_shl(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    let (high, low) = split_shift_amt(ctx, args[1].w(), args[1].bits().to_owned());
    Enc::Bits(shift_bv_bits(
        ctx,
        args[0].uint().0,
        low,
        None,
        args[0].w(),
        high,
    ))
}

fn bv_ashr(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    let (high, low) = split_shift_amt(ctx, args[1].w(), args[1].bits().to_owned());
    let rev_data = bit_join(ctx.field(), args[0].bits().into_iter().rev().cloned());
    Enc::Bits(
        shift_bv_bits(
            ctx,
            rev_data,
            low,
            args[0].bits().last().cloned(),
            args[0].w(),
            high,
        )
        .into_iter()
        .rev()
        .collect(),
    )
}

fn bv_lshr(ctx: &mut Ctx, _op: &Op, args: &[&Enc]) -> Enc {
    let (high, low) = split_shift_amt(ctx, args[1].w(), args[1].bits().to_owned());
    let rev_data = bit_join(ctx.field(), args[0].bits().into_iter().rev().cloned());
    Enc::Bits(
        shift_bv_bits(
            ctx,
            rev_data,
            low,
            None,
            args[0].w(),
            high,
        )
        .into_iter()
        .rev()
        .collect(),
    )
}

/// The boolean/bv -> field rewrite rules.
pub fn rules() -> Vec<Rule<Enc>> {
    use EncTypes::*;
    use OpPat as OpP;
    use SortPat::{BitVector as BV, Bool, Field as Ff};
    use Ty::*;
    vec![
        Rule::new(0, OpP::Const, Bool, All(Bit), bool_const),
        Rule::new(0, OpP::Eq, Bool, All(Bit), bool_eq),
        Rule::new(0, OpP::Ite, Bool, All(Bit), bool_ite),
        Rule::new(0, OpP::Not, Bool, All(Bit), not),
        Rule::new(0, OpP::BoolMaj, Bool, All(Bit), maj),
        Rule::new(0, OpP::Implies, Bool, All(Bit), implies),
        Rule::new(0, OpP::BoolNaryOp(BoolNaryOp::Xor), Bool, All(Bit), xor),
        Rule::new(0, OpP::BoolNaryOp(BoolNaryOp::Or), Bool, All(Bit), or),
        Rule::new(0, OpP::BoolNaryOp(BoolNaryOp::And), Bool, All(Bit), and),
        Rule::new(0, OpP::Const, BV, All(Bit), bv_const),
        Rule::new(0, OpP::BvBit, BV, All(Bits), bv_bit),
        Rule::new(0, OpP::Ite, BV, Seq(vec![Bit, Uint, Uint]), bv_ite),
        Rule::new(0, OpP::BvUnOp(BvUnOp::Not), BV, All(Bits), bv_not),
        Rule::new(0, OpP::BvUnOp(BvUnOp::Neg), BV, All(Uint), bv_neg),
        Rule::new(0, OpP::Eq, BV, All(Uint), bv_eq),
        Rule::new(0, OpP::BvUext, BV, All(Bits), bv_uext_bits),
        Rule::new(1, OpP::BvUext, BV, All(Uint), bv_uext_uint),
        Rule::new(0, OpP::BvSext, BV, All(Bits), bv_sext),
        Rule::new(0, OpP::BoolToBv, BV, All(Bit), bool_to_bv),
        Rule::new(0, OpP::BvNaryOp(BvNaryOp::And), BV, All(Bits), bv_and),
        Rule::new(0, OpP::BvNaryOp(BvNaryOp::Or), BV, All(Bits), bv_or),
        Rule::new(0, OpP::BvNaryOp(BvNaryOp::Xor), BV, All(Bits), bv_xor),
        Rule::new(0, OpP::BvNaryOp(BvNaryOp::Add), BV, All(Uint), bv_add),
        Rule::new(0, OpP::BvNaryOp(BvNaryOp::Mul), BV, All(Uint), bv_mul),
        Rule::new(0, OpP::BvBinOp(BvBinOp::Sub), BV, All(Uint), bv_sub),
        Rule::new(0, OpP::BvBinOp(BvBinOp::Udiv), BV, All(Uint), bv_udiv),
        Rule::new(0, OpP::BvBinOp(BvBinOp::Urem), BV, All(Uint), bv_urem),
        Rule::new(
            0,
            OpP::BvBinOp(BvBinOp::Shl),
            BV,
            Seq(vec![Uint, Bits]),
            bv_shl,
        ),
        Rule::new(0, OpP::BvBinOp(BvBinOp::Ashr), BV, All(Bits), bv_ashr),
        Rule::new(0, OpP::BvBinOp(BvBinOp::Lshr), BV, All(Bits), bv_lshr),
        Rule::new(0, OpP::BvBinPred(BvBinPred::Uge), BV, All(Uint), bv_uge),
        Rule::new(0, OpP::BvBinPred(BvBinPred::Ugt), BV, All(Uint), bv_ugt),
        Rule::new(0, OpP::BvBinPred(BvBinPred::Ule), BV, All(Uint), bv_ule),
        Rule::new(0, OpP::BvBinPred(BvBinPred::Ult), BV, All(Uint), bv_ult),
        Rule::new(0, OpP::BvBinPred(BvBinPred::Sge), BV, All(Bits), bv_sge),
        Rule::new(0, OpP::BvBinPred(BvBinPred::Sgt), BV, All(Bits), bv_sgt),
        Rule::new(0, OpP::BvBinPred(BvBinPred::Sle), BV, All(Bits), bv_sle),
        Rule::new(0, OpP::BvBinPred(BvBinPred::Slt), BV, All(Bits), bv_slt),
        Rule::new(0, OpP::BvExtract, BV, All(Bits), bv_extract),
        Rule::new(0, OpP::BvConcat, BV, All(Bits), bv_concat),
        Rule::new(0, OpP::PfToBv, BV, All(Field), pf_to_bv),
        Rule::new(0, OpP::PfNaryOp(PfNaryOp::Add), Ff, All(Field), pf_add),
        Rule::new(0, OpP::PfNaryOp(PfNaryOp::Mul), Ff, All(Field), pf_mul),
        Rule::new(0, OpP::PfUnOp(PfUnOp::Neg), Ff, All(Field), pf_neg),
        Rule::new(0, OpP::PfUnOp(PfUnOp::Recip), Ff, All(Field), pf_recip),
        // TODO: timeout
        // Rule::new(0, OpP::UbvToPf, Ff, All(Uint), ubv_to_pf),
        // TODO: timeout
        // Rule::new(0, OpP::Const, Ff, All(Field), pf_const),
        Rule::new(0, OpP::Ite, Ff, Seq(vec![Bit, Field, Field]), pf_ite),
    ]
}

/// Our encoding choice function
pub fn choose(t: &Term, encs: &[&BTreeSet<Ty>]) -> usize {
    match &t.op {
        Op::BvUext(_) => {
            if encs[0].contains(&Ty::Bits) {
                1
            } else {
                0
            }
        }
        o => panic!("Cannot choose for op {}", o),
    }
}
