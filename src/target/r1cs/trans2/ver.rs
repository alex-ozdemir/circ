//! Verification machinery
use super::lang::{RewriteCtx, Rule};
use crate::ir::term::*;
use circ_fields::FieldT;

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

/// Given a boolean term and a field term that purportedly encodes it, returns a term that is true
/// iff the encoding is valid.
pub fn bool_enc_valid(b: &Term, f: &Term) -> Term {
    let field = FieldT::from(check(f).as_pf());
    let f_valid = term![EQ; term![PF_MUL; f.clone(), f.clone()], f.clone()];
    let f_is_1 = term![EQ; f.clone(), pf_lit(field.new_v(1))];
    term![AND; f_valid, term![EQ; b.clone(), f_is_1]]
}

/// Create QF_FF formulas that are SAT iff this rule is unsound.
pub fn bool_soundness_terms(rule: &Rule, max_args: usize, field: &FieldT) -> Vec<(Term, Term)> {
    assert_eq!(rule.pattern().1, Sort::Bool);
    let mut out = Vec::new();
    for op in rule.pattern().get_ops() {
        for vars in generate_inputs(&op, max_args) {
            let mut assertions = Vec::new();

            // create boolean inputs and term
            let bool_args: Vec<Term> = vars
                .iter()
                .map(|n| leaf_term(Op::Var(n.clone(), Sort::Bool)))
                .collect();
            let bool_term = term(op.clone(), bool_args.clone());

            // validly encode them
            let ff_args: Vec<Term> = vars
                .iter()
                .map(|n| leaf_term(Op::Var(format!("{}_ff", n), Sort::Field(field.clone()))))
                .collect();
            for (b, f) in bool_args.iter().zip(&ff_args) {
                assertions.push(bool_enc_valid(b, f))
            }

            // apply the lowering rule
            let mut ctx = RewriteCtx::new(field.clone());
            let ff_term = rule.apply(&mut ctx, &bool_term, &ff_args);
            assertions.extend(ctx.assertions); // save the assertions

            // assert that the output is mal-encoded
            assertions.push(term![NOT; bool_enc_valid(&bool_term, &ff_term)]);

            out.push((bool_term, term(AND, assertions)))
        }
    }
    out
}
