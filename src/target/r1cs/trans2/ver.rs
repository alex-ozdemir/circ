//! Verification machinery
#[allow(unused_imports)]
use super::lang::{Encoding, EncodingType, OpPattern, RewriteCtx, Rule, SortPattern};
use crate::ir::term::*;
use circ_fields::FieldT;
use std::collections::BTreeSet;
use std::iter::repeat;

/// An encoding scheme with formalized semantics.
pub trait VerifiableEncoding: Encoding {
    /// Given a term `t` and encoded form `self`, return a boolean term which is true iff the
    /// encoding is valid.
    fn is_valid(&self, t: Term) -> Term;
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
        OpPattern::Const => s.elems_iter_values().map(Op::Const).collect(),
        OpPattern::Eq => vec![Op::Eq],
        OpPattern::Ite => vec![Op::Ite],
        OpPattern::Not => vec![Op::Not],
        OpPattern::BoolMaj => vec![Op::BoolMaj],
        OpPattern::Implies => vec![Op::Implies],
        OpPattern::BoolNaryOp(o) => vec![Op::BoolNaryOp(*o)],
        OpPattern::PfUnOp(o) => vec![Op::PfUnOp(*o)],
        OpPattern::PfNaryOp(o) => vec![Op::PfNaryOp(*o)],
        OpPattern::BvBit => (0..s.as_bv()).map(|i| Op::BvBit(i)).collect(),
        OpPattern::BvBinOp(o) => vec![Op::BvBinOp(*o)],
        OpPattern::BvBinPred(o) => vec![Op::BvBinPred(*o)],
        OpPattern::BvNaryOp(o) => vec![Op::BvNaryOp(*o)],
        OpPattern::BvUnOp(o) => vec![Op::BvUnOp(*o)],
        OpPattern::BoolToBv => vec![Op::BoolToBv],
        OpPattern::BvExtract => todo!(),
        OpPattern::BvConcat => todo!(),
        OpPattern::BvUext => (0..s.as_bv()).map(|i| Op::BvUext(i)).collect(),
        OpPattern::BvSext => (0..s.as_bv()).map(|i| Op::BvSext(i)).collect(),
        OpPattern::PfToBv => todo!(),
    }
}

/// Get all argument sort sequences for a given operator
/// and sort parameter.
fn arg_sorts(o: &Op, s: &Sort, bnd: &Bound) -> Vec<Vec<Sort>> {
    match o {
        Op::Eq => vec![vec![s.clone(), s.clone()]],
        Op::Ite => vec![vec![Sort::Bool, s.clone(), s.clone()]],
        Op::BvUext(i) | Op::BvSext(i) => vec![vec![Sort::BitVector(s.as_bv() - i)]],
        Op::BoolToBv => vec![vec![Sort::Bool]],
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
/// Each returned tuple is `(term, sort, completeness)` where:
///
/// * `term` is a term comprising a single operator application that `rule` would apply to
/// * `sort` is the sort that the term's operator may be parameterized on
/// * `completeness` is a boolean term that is SAT iff the rule is unsound.
pub fn soundness_terms<E: VerifiableEncoding>(
    rule: &Rule<E>,
    bnd: &Bound,
    field: &FieldT,
) -> Vec<(Term, Sort, Term)> {
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
                    .enumerate()
                    .map(|(i, ((name, sort), b))| {
                        let e = E::variable(&mut ctx, name, sort, rule.encoding_ty(i));
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

                out.push((t, sort.clone(), mk_and(assertions)))
            }
        }
    }
    out
}

/// Create formulas that are SAT iff this rule is incomplete.
///
/// Each returned tuple is `(term, sort, completeness)` where:
///
/// * `term` is a term comprising a single operator application that `rule` would apply to
/// * `sort` is the sort that the term's operator may be parameterized on
/// * `completeness` is a boolean term that is SAT iff the rule is incomplete.
pub fn completeness_terms<E: VerifiableEncoding>(
    rule: &Rule<E>,
    bnd: &Bound,
    field: &FieldT,
) -> Vec<(Term, Sort, Term)> {
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
                    .enumerate()
                    .map(|(i, (n, s))| E::variable(&mut ctx, n, s, rule.encoding_ty(i)))
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

                out.push((t, sort.clone(), mk_and(assertions)))
            }
        }
    }
    out
}

/// Create formulas that are SAT iff some variable rule is unsound.
///
/// Each returned tuple is `(sort, soundness)` where:
///
/// * `sort` is the sort that the term's operator may be parameterized on
/// * `soundness` is a boolean term that is SAT iff the rule is unsound.
pub fn v_soundness_terms<E: VerifiableEncoding>(bnd: &Bound, field: &FieldT) -> Vec<(Sort, Term)> {
    let mut out = Vec::new();
    let sort_patterns: BTreeSet<SortPattern> = <E::Type as EncodingType>::all()
        .into_iter()
        .map(|t| t.sort())
        .collect();
    for sort_pattern in sort_patterns {
        for sort in sorts(&sort_pattern, bnd) {
            let mut ctx = RewriteCtx::new(field.clone());
            let name = "a".to_owned();
            let e = E::d_variable(&mut ctx, &name, &sort);
            let var = leaf_term(Op::Var(name.clone(), sort.clone()));
            let no_valid = term![NOT; term![Op::Quant(Quant {
                ty: QuantType::Exists,
                bindings: vec![(name, sort.clone())],
            }); e.is_valid(var)]];
            let mut assertions = ctx.assertions;
            assertions.push(no_valid);
            out.push((sort, mk_and(assertions)));
        }
    }
    out
}

/// Create formulas that are SAT iff some variable rule is incomplete.
///
/// Each returned tuple is `(sort, term)` where:
///
/// * `sort` is the sort that the term's operator may be parameterized on
/// * `term` is a boolean term that is SAT iff the rule is incomplete.
pub fn v_completeness_terms<E: VerifiableEncoding>(
    bnd: &Bound,
    field: &FieldT,
) -> Vec<(Sort, Term)> {
    let mut out = Vec::new();
    let sort_patterns: BTreeSet<SortPattern> = <E::Type as EncodingType>::all()
        .into_iter()
        .map(|t| t.sort())
        .collect();
    for sort_pattern in sort_patterns {
        for sort in sorts(&sort_pattern, bnd) {
            let mut ctx = RewriteCtx::new(field.clone());
            let name = "a".to_owned();
            let _e = E::d_variable(&mut ctx, &name, &sort);
            let mut assertions = Vec::new();

            // assert the pre-compute is correct
            for (val, name) in ctx.new_variables {
                let var = leaf_term(Op::Var(name, check(&val)));
                assertions.push(term![EQ; var, val]);
            }

            assertions.push(term![NOT; mk_and(ctx.assertions)]);

            out.push((sort, mk_and(assertions)));
        }
    }
    out
}

/// Create formulas that are SAT iff some conversion rule is unsound.
///
/// Each returned tuple is `(from, to, soundness)` where:
///
/// * `from` is the initial encoding
/// * `to` is the final encoding
/// * `soundness` is a boolean term that is SAT iff the rule is unsound.
pub fn c_soundness_terms<E: VerifiableEncoding>(
    bnd: &Bound,
    field: &FieldT,
) -> Vec<(E::Type, E::Type, Sort, Term)> {
    let mut out = Vec::new();
    for from in <E::Type as EncodingType>::all() {
        for to in <E::Type as EncodingType>::all() {
            if from != to && from.sort() == to.sort() {
                for sort in sorts(&from.sort(), bnd) {
                    let mut ctx = RewriteCtx::new(field.clone());
                    let name = "a".to_owned();
                    let e = E::variable(&mut ctx, &name, &sort, from);
                    let var = leaf_term(Op::Var(name, sort.clone()));
                    // assert the pre-compute is correct
                    for (val, name) in ctx.new_variables.drain(..) {
                        let var = leaf_term(Op::Var(name, check(&val)));
                        ctx.assertions.push(term![EQ; var, val]);
                    }
                    let e2 = e.convert(&mut ctx, to);
                    let is_valid = e2.is_valid(var);
                    let mut assertions = ctx.assertions;
                    assertions.push(term![NOT; is_valid]);
                    out.push((from, to, sort, mk_and(assertions)));
                }
            }
        }
    }
    out
}

/// Create formulas that are SAT iff some conversion rule is unsound.
///
/// Each returned tuple is `(from, to, soundness)` where:
///
/// * `from` is the initial encoding
/// * `to` is the final encoding
/// * `soundness` is a boolean term that is SAT iff the rule is unsound.
pub fn c_completeness_terms<E: VerifiableEncoding>(
    bnd: &Bound,
    field: &FieldT,
) -> Vec<(E::Type, E::Type, Sort, Term)> {
    let mut out = Vec::new();
    for from in <E::Type as EncodingType>::all() {
        for to in <E::Type as EncodingType>::all() {
            if from != to && from.sort() == to.sort() {
                for sort in sorts(&from.sort(), bnd) {
                    let mut ctx = RewriteCtx::new(field.clone());
                    let name = "a".to_owned();
                    let e = E::variable(&mut ctx, &name, &sort, from);
                    let _e2 = e.convert(&mut ctx, to);
                    let mut assertions = Vec::new();

                    // assert the pre-compute is correct
                    for (val, name) in ctx.new_variables.drain(..) {
                        let var = leaf_term(Op::Var(name, check(&val)));
                        assertions.push(term![EQ; var, val]);
                    }

                    assertions.push(term![NOT; mk_and(ctx.assertions)]);

                    out.push((from, to, sort, mk_and(assertions)));
                }
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
