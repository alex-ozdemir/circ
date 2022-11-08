//! Rules for lowering booleans and bit-vectors to a field

use super::lang::{EncTypes, Encoding, EncodingType, OpPattern, RewriteCtx, Rule, SortPattern};
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
    Uint(Term, usize),
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

impl EncodingType for Ty {
    fn sort(&self) -> SortPattern {
        match self {
            Ty::Bit => SortPattern::Bool,
            Ty::Bits => SortPattern::BitVector,
            Ty::Uint => SortPattern::BitVector,
        }
    }

    fn all() -> Vec<Self> {
        vec![Self::Bit, Self::Bits, Self::Uint]
    }

    fn default_for_sort(s: &Sort) -> Self {
        match s {
            Sort::Bool => Ty::Bit,
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
    #[allow(dead_code)]
    pub(super) fn uint(&self) -> (Term, usize) {
        match self {
            Enc::Uint(b, u) => (b.clone(), *u),
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

    fn variable(ctx: &mut RewriteCtx, name: &str, sort: &Sort, ty: Ty) -> Self {
        assert_eq!(SortPattern::from(sort), ty.sort());
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
        }
    }

    fn convert(&self, ctx: &mut RewriteCtx, to: Self::Type) -> Self {
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

fn is_zero(ctx: &mut RewriteCtx, x: Term) -> Term {
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

fn ensure_bit(ctx: &mut RewriteCtx, b: Term) {
    let b_minus_one = term![PF_ADD; b.clone(), term![PF_NEG; ctx.one().clone()]];
    ctx.assert(term![EQ; term![PF_MUL; b_minus_one, b], ctx.zero().clone()]);
}

fn bit_split(ctx: &mut RewriteCtx, reason: &str, x: Term, n: usize) -> Vec<Term> {
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

fn or_helper(ctx: &mut RewriteCtx, mut args: Vec<Term>) -> Term {
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

fn or(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(or_helper(ctx, args.iter().map(|a| a.bit()).collect()))
}

fn and(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(or_helper(
        ctx,
        args.iter().map(|a| bool_neg(a.bit())).collect(),
    )))
}

fn bool_eq(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(term![PF_ADD;
        ctx.one().clone(),
        term![PF_NEG; args[0].bit()],
        term![PF_NEG; args[1].bit()],
        term![PF_MUL; ctx.f_const(2), args[0].bit(), args[1].bit()]])
}

fn xor(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
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
                let bits = bit_split(ctx, "xor", partial_sum, num_bits);
                args.push(bits.into_iter().next().unwrap());
            }
        };
    })
}

fn not(_ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(args[0].bit()))
}

fn implies(_ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(bool_neg(
        term![PF_MUL; args[0].bit(), bool_neg(args[1].bit())],
    ))
}

fn ite(c: Term, t: Term, f: Term) -> Term {
    term![PF_ADD; term![PF_MUL; c, term![PF_ADD; t, term![PF_NEG; f.clone()]]], f]
}

fn bool_ite(_ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bit(ite(args[0].bit(), args[1].bit(), args[2].bit()))
}

fn bool_const(ctx: &mut RewriteCtx, op: &Op, _args: &[&Enc]) -> Enc {
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

fn maj(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
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

fn bv_bit(_ctx: &mut RewriteCtx, op: &Op, args: &[&Enc]) -> Enc {
    if let Op::BvBit(i) = op {
        Enc::Bit(args[0].bits()[*i].clone())
    } else {
        unreachable!()
    }
}

fn bv_const(ctx: &mut RewriteCtx, op: &Op, _args: &[&Enc]) -> Enc {
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

fn bv_ite(_ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Uint(
        ite(args[0].bit(), args[1].uint().0, args[2].uint().0),
        args[1].uint().1,
    )
}

fn bv_not(_ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    Enc::Bits(args[0].bits().iter().map(|b| bool_neg(b.clone())).collect())
}

fn bv_neg(ctx: &mut RewriteCtx, _op: &Op, args: &[&Enc]) -> Enc {
    let (x, w) = args[0].uint();
    let field = FieldT::from(check(&x).as_pf());
    let zero = is_zero(ctx, x.clone());
    let diff = term![PF_ADD; pf_lit(field.new_v(Integer::from(1) << w)), term![PF_NEG; x]];
    Enc::Uint(ite(zero, pf_lit(field.new_v(0)), diff), w)
}

/// The boolean/bv -> field rewrite rules.
pub fn rules() -> Vec<Rule<Enc>> {
    use EncTypes::*;
    use OpPattern as OpP;
    use SortPattern::{BitVector, Bool};
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
        Rule::new(0, OpP::Const, BitVector, All(Bit), bv_const),
        Rule::new(0, OpP::BvBit, BitVector, All(Bits), bv_bit),
        Rule::new(0, OpP::Ite, BitVector, Seq(vec![Bit, Uint, Uint]), bv_ite),
        Rule::new(0, OpP::BvUnOp(BvUnOp::Not), BitVector, All(Bits), bv_not),
        Rule::new(0, OpP::BvUnOp(BvUnOp::Neg), BitVector, All(Uint), bv_neg),
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
