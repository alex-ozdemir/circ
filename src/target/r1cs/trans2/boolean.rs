//! Rules for lowering booleans to a field

use super::lang::{OpPattern, RewriteCtx, Rule};
use crate::ir::term::*;

use circ_fields::FieldT;
use rug::Integer;

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
    // m * x - 1 + is_zero == 0
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

fn rw_or_helper(ctx: &mut RewriteCtx, mut l_args: Vec<Term>) -> Term {
    loop {
        match l_args.len() {
            0 => return ctx.zero().clone(),
            1 => return l_args.pop().unwrap(),
            2 => {
                return bool_neg(
                    term![PF_MUL; bool_neg(l_args[0].clone()), bool_neg(l_args[1].clone())],
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
                    term(PF_ADD, l_args.drain(i - take..).collect()),
                ));

                l_args.push(new);
            }
        };
    }
}

fn rw_or(ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    rw_or_helper(ctx, l_args.to_owned())
}

fn rw_and(ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    bool_neg(rw_or_helper(
        ctx,
        l_args.iter().map(|a| bool_neg(a.clone())).collect(),
    ))
}

fn rw_bool_eq(ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    term![PF_ADD;
        ctx.one().clone(),
        term![PF_NEG; l_args[0].clone()],
        term![PF_NEG; l_args[1].clone()],
        term![PF_MUL; ctx.f_const(2), l_args[0].clone(), l_args[1].clone()]]
}

fn rw_xor(ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    let mut l_args = l_args.to_owned();
    loop {
        match l_args.len() {
            0 => return ctx.zero().clone(),
            1 => return l_args.pop().unwrap(),
            2 => {
                return term![PF_ADD;
                    l_args[0].clone(),
                    l_args[1].clone(),
                    term![PF_NEG; term![PF_MUL; ctx.f_const(2), l_args[0].clone(), l_args[1].clone()]]]
            }
            i => {
                // assumes field is prime
                let take = if ctx.field().modulus() < &i {
                    ctx.field().modulus().to_usize().unwrap()
                } else {
                    i
                };
                let partial_sum = term(PF_ADD, l_args.drain(i - take..).collect());
                let num_bits = ((partial_sum.cs.len() as f64) + 0.2f64).log2() as usize + 1;
                let bits = rw_bit_split(ctx, "xor", partial_sum, num_bits);
                l_args.push(bits.into_iter().next().unwrap());
            }
        };
    }
}

fn rw_not(_ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    bool_neg(l_args[0].clone())
}

fn rw_implies(_ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    bool_neg(term![PF_MUL; l_args[0].clone(), bool_neg(l_args[1].clone())])
}

fn rw_var(ctx: &mut RewriteCtx, term: &Term, _l_args: &[Term]) -> Term {
    if let Op::Var(name, sort) = &term.op {
        assert_eq!(sort, &Sort::Bool);
        let f_var = ctx.fresh(&name, bool_to_field(term.clone(), &ctx.field()));
        rw_ensure_bit(ctx, f_var.clone());
        f_var
    } else {
        unreachable!()
    }
}

fn rw_const(ctx: &mut RewriteCtx, term: &Term, _l_args: &[Term]) -> Term {
    if let Op::Const(Value::Bool(b)) = &term.op {
        if *b {
            ctx.one().clone()
        } else {
            ctx.zero().clone()
        }
    } else {
        unreachable!()
    }
}

/// The boolean -> field rewrite rules.
pub fn rules() -> Vec<Rule> {
    use OpPattern as OpP;
    use Sort::Bool;
    vec![
        Rule::new(OpP::Const, Bool, Box::new(rw_const)),
        Rule::new(OpP::Var, Bool, Box::new(rw_var)),
        Rule::new(OpP::Eq, Bool, Box::new(rw_bool_eq)),
        Rule::new(OpP::Not, Bool, Box::new(rw_not)),
        Rule::new(OpP::Implies, Bool, Box::new(rw_implies)),
        Rule::new(OpP::BoolNaryOp(BoolNaryOp::Xor), Bool, Box::new(rw_xor)),
        Rule::new(OpP::BoolNaryOp(BoolNaryOp::Or), Bool, Box::new(rw_or)),
        Rule::new(OpP::BoolNaryOp(BoolNaryOp::And), Bool, Box::new(rw_and)),
    ]
}
