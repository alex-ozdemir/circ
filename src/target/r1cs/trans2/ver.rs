//! Verification machinery
use super::boolean::Enc;
use super::lang::{Encoding, RewriteCtx, Rule, SortPattern};
use crate::ir::term::*;
use circ_fields::FieldT;

/// An encoding scheme with formalized semantics.
trait VerifiableEncoding: Encoding {
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

/// Generate all sequences of variables that could be arguments to this operator.
fn generate_inputs(op: &Op, max_args: usize) -> Vec<Vec<String>> {
    fn nth_name(mut n: usize) -> String {
        let mut o = String::new();
        n += 1;
        while n > 0 {
            o.push((b'a' + (n % 26) as u8) as char);
            n /= 26;
        }
        o
    }
    if let Some(n_args) = op.arity() {
        vec![(0..n_args).map(nth_name).collect()]
    } else {
        (1..max_args)
            .map(|n| (0..n).map(nth_name).collect())
            .collect()
    }
}

/// Create QF_FF formulas that are SAT iff this rule is unsound.
pub fn bool_soundness_terms(
    rule: &Rule<super::boolean::Enc>,
    max_args: usize,
    field: &FieldT,
) -> Vec<(Term, Term)> {
    assert_eq!(rule.pattern().1, SortPattern::Bool);
    let mut out = Vec::new();
    for op in rule.pattern().get_ops(4) {
        for vars in generate_inputs(&op, max_args) {
            let mut assertions = Vec::new();

            // create boolean inputs and term
            let bool_args: Vec<Term> = vars
                .iter()
                .map(|n| leaf_term(Op::Var(n.clone(), Sort::Bool)))
                .collect();
            let bool_term = term(op.clone(), bool_args.clone());

            // validly encode them
            let mut ctx = RewriteCtx::new(field.clone());
            let e_args: Vec<Enc> = vars
                .iter()
                .zip(&bool_args)
                .map(|(v, b)| {
                    let e = Enc::variable(&mut ctx, v, &Sort::Bool);
                    assertions.push(e.is_valid(b.clone()));
                    e
                })
                .collect();

            // apply the lowering rule
            let ff_term = rule.apply(&mut ctx, &bool_term.op, &e_args.iter().collect::<Vec<_>>());
            assertions.extend(ctx.assertions); // save the assertions

            // assert that the output is mal-encoded
            assertions.push(term![NOT; ff_term.is_valid(bool_term.clone())]);

            out.push((bool_term, term(AND, assertions)))
        }
    }
    out
}
