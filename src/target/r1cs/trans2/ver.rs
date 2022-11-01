//! Verification machinery
use super::boolean::Enc;
use super::lang::{Encoding, OpPattern, RewriteCtx, Rule, SortPattern};
use crate::ir::term::*;
use circ_fields::FieldT;
use std::iter::repeat;

/// An encoding scheme with formalized semantics.
pub trait VerifiableEncoding: Encoding {
    /// Given a term `t` and encoded form `self`, return a boolean term which is true iff the
    /// encoding is valid.
    fn is_valid(&self, t: Term) -> Term;
}

impl VerifiableEncoding for Enc {
    fn is_valid(&self, t: Term) -> Term {
        match self {
            Enc::Bit(f) => {
                let field = FieldT::from(check(f).as_pf());
                let f_valid = term![EQ; term![PF_MUL; f.clone(), f.clone()], f.clone()];
                let f_is_1 = term![EQ; f.clone(), pf_lit(field.new_v(1))];
                term![AND; f_valid, term![EQ; t.clone(), f_is_1]]
            }
        }
    }
}

/// A bound for verification
pub struct Bound {
    /// The maximum number of operator arguments
    pub args: usize,
    /// The maximum size of bitvectors
    pub bv_bits: usize,
}

/// Get all sorts for a [SortPattern]
fn sorts(s: &SortPattern, bnd: &Bound) -> Vec<Sort> {
    match s {
        SortPattern::BitVector => (1..=bnd.bv_bits).map(Sort::BitVector).collect(),
        SortPattern::Bool => vec![Sort::Bool],
    }
}

/// Get all operators that would match this [Pattern].
fn ops(o: &OpPattern, s: &Sort) -> Vec<Op> {
    match o {
        OpPattern::Const => {
            let iter = s.elems_iter_values();
            assert!(iter.size_hint().1.is_some(), "Infinite set");
            iter.map(Op::Const).collect()
        }
        OpPattern::Eq => vec![Op::Eq],
        OpPattern::Ite => vec![Op::Ite],
        OpPattern::Not => vec![Op::Not],
        OpPattern::BoolMaj => vec![Op::BoolMaj],
        OpPattern::Implies => vec![Op::Implies],
        OpPattern::BoolNaryOp(o) => vec![Op::BoolNaryOp(*o)],
        OpPattern::PfUnOp(o) => vec![Op::PfUnOp(*o)],
        OpPattern::PfNaryOp(o) => vec![Op::PfNaryOp(*o)],
    }
}

/// Get all argument sort sequences for a given operator
/// and sort parameter.
fn arg_sorts(o: &Op, s: &Sort, bnd: &Bound) -> Vec<Vec<Sort>> {
    match o {
        Op::Eq => vec![vec![s.clone(), s.clone()]],
        Op::Ite => vec![vec![Sort::Bool, s.clone(), s.clone()]],
        _ => {
            if let Some(n_args) = o.arity() {
                vec![repeat(s).take(n_args).cloned().collect()]
            } else {
                (1..=bnd.args)
                    .map(|n| repeat(s).take(n).cloned().collect())
                    .collect()
            }
        }
    }
}

/// Generate names for some sorts
fn gen_names(sorts: Vec<Sort>) -> Vec<(String, Sort)> {
    fn nth_name(mut n: usize) -> String {
        let mut o = String::new();
        loop {
            o.push((b'a' + (n % 26) as u8) as char);
            n /= 26;
            if n == 0 {
                return o;
            }
        }
    }
    sorts
        .into_iter()
        .enumerate()
        .map(|(i, s)| (nth_name(i), s))
        .collect()
}

/// Create formulas that are SAT iff this rule is unsound.
///
/// Each returned tuple is `(term, soundness)` where `term` is a term comprising a single operator
/// application that `rule` would apply to, and `soundness` is a boolean term that is SAT iff the
/// rule if unsound.
pub fn soundness_terms<E: VerifiableEncoding>(
    rule: &Rule<E>,
    bnd: &Bound,
    field: &FieldT,
) -> Vec<(Term, Term)> {
    let mut out = Vec::new();
    for sort in sorts(&rule.pattern().1, bnd) {
        for op in ops(&rule.pattern().0, &sort) {
            for arg_sorts in arg_sorts(&op, &sort, bnd) {
                let var_parts = gen_names(arg_sorts);
                let mut assertions = Vec::new();

                // create inputs
                let args: Vec<Term> = var_parts
                    .iter()
                    .map(|(n, s)| leaf_term(Op::Var(n.clone(), s.clone())))
                    .collect();

                // validly encode them
                let mut ctx = RewriteCtx::new(field.clone());
                let e_args: Vec<E> = var_parts
                    .iter()
                    .zip(&args)
                    .map(|((name, sort), b)| {
                        let e = E::variable(&mut ctx, name, sort);
                        assertions.push(e.is_valid(b.clone()));
                        e
                    })
                    .collect();

                // apply the lowering rule
                let t = term(op.clone(), args.clone());
                let e_t = rule.apply(&mut ctx, &t.op, &e_args.iter().collect::<Vec<_>>());
                assertions.extend(ctx.assertions); // save the assertions

                // assert that the output is mal-encoded
                assertions.push(term![NOT; e_t.is_valid(t.clone())]);

                out.push((t, mk_and(assertions)))
            }
        }
    }
    out
}

/// Create formulas that are SAT iff this rule is incomplete.
///
/// Each returned tuple is `(term, completeness)` where `term` is a term comprising a single
/// operator application that `rule` would apply to, and `completeness` is a boolean term that is
/// SAT iff the rule if incomplete.
pub fn completeness_terms<E: VerifiableEncoding>(
    rule: &Rule<E>,
    bnd: &Bound,
    field: &FieldT,
) -> Vec<(Term, Term)> {
    let mut out = Vec::new();
    for sort in sorts(&rule.pattern().1, bnd) {
        for op in ops(&rule.pattern().0, &sort) {
            for arg_sorts in arg_sorts(&op, &sort, bnd) {
                let var_parts = gen_names(arg_sorts);
                let mut assertions = Vec::new();

                // create inputs
                let args: Vec<Term> = var_parts
                    .iter()
                    .map(|(n, s)| leaf_term(Op::Var(n.clone(), s.clone())))
                    .collect();

                // encode them
                let mut ctx = RewriteCtx::new(field.clone());
                let e_args: Vec<E> = var_parts
                    .iter()
                    .map(|(name, sort)| E::variable(&mut ctx, name, sort))
                    .collect();

                // apply the lowering rule
                let t = term(op.clone(), args.clone());
                let _e_t = rule.apply(&mut ctx, &t.op, &e_args.iter().collect::<Vec<_>>());

                // assert the pre-compute is correct
                for (val, name) in ctx.new_variables {
                    let var = leaf_term(Op::Var(name, check(&val)));
                    assertions.push(term![EQ; var, val]);
                }

                // assert that some contraint is broken
                assertions.push(term![NOT; mk_and(ctx.assertions)]);

                out.push((t, mk_and(assertions)))
            }
        }
    }
    out
}

fn mk_and(mut ts: Vec<Term>) -> Term {
    match ts.len() {
        0 => bool_lit(true),
        1 => ts.pop().unwrap(),
        _ => term(AND, ts),
    }
}
