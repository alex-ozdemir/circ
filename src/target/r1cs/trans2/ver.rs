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

/// Create QF_FF formulas that are SAT iff this rule is unsound.
pub fn bool_soundness_terms(rule: &Rule, max_args: usize, field: &FieldT) -> Vec<Term> {
    assert_eq!(rule.pattern().1, Sort::Bool);
    let vars_s = generate_inputs(&rule.pattern().get_op(), max_args);
    vars_s
        .into_iter()
        .map(|vars| {
            let bool_args: Vec<Term> = vars
                .iter()
                .map(|n| leaf_term(Op::Var(n.clone(), Sort::Bool)))
                .collect();
            let ff_args: Vec<Term> = vars
                .iter()
                .map(|n| leaf_term(Op::Var(format!("{}_ff", n), Sort::Field(field.clone()))))
                .collect();
            let mut ctx = RewriteCtx::new(field.clone());
            for f in &ff_args {
                ctx.assert(term![EQ; term![PF_MUL; f.clone(), f.clone()], f.clone()]);
            }
            let bool_term = term(rule.pattern().get_op(), bool_args.clone());
            let ff_term = rule.apply(&mut ctx, &bool_term, &ff_args);
            let mut assertions = Vec::new();
            for (b, f) in bool_args.into_iter().zip(ff_args) {
                assertions.push(term![EQ; b, term![EQ; f, ctx.one().clone()]]);
            }
            let zero_out = term![EQ; ff_term.clone(), ctx.zero().clone()];
            let one_out = term![EQ; ff_term.clone(), ctx.one().clone()];
            let malencoded_out = term![NOT; term![OR; zero_out, one_out.clone()]];
            let wrong_out = term![NOT; term![EQ; bool_term, one_out]];
            assertions.extend(ctx.assertions);
            assertions.push(term![OR; malencoded_out, wrong_out]);
            term(AND, assertions)
        })
        .collect()
}
