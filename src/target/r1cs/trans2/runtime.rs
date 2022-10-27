use super::lang::{Pattern, RewriteCtx, Rule};
use crate::ir::term::*;
use circ_fields::FieldT;

use fxhash::FxHashMap as HashMap;

/// Apply some rules to translated a computation into a field.
pub fn apply_rules(rs: Vec<Rule>, field: &FieldT, mut computation: Computation) -> Computation {
    assert!(computation.outputs.len() == 1);
    let mut rule_table: HashMap<Pattern, Rule> = HashMap::default();
    for r in rs {
        let prev = rule_table.insert(r.pattern().clone(), r);
        if let Some(p) = prev {
            panic!("Two rules for {:?}", p.pattern())
        }
    }
    let mut rewrite_table: TermMap<Term> = Default::default();
    let mut ctx = RewriteCtx::new(field.clone());
    for t in computation.terms_postorder() {
        let p = Pattern::from(&t);
        let r = rule_table
            .get(&p)
            .unwrap_or_else(|| panic!("No pattern for pattern {:?}", p));
        let args: Vec<Term> =
            t.cs.iter()
                .map(|c| rewrite_table.get(c).unwrap().clone())
                .collect();
        let new = r.apply(&mut ctx, &t, &args);
        rewrite_table.insert(t, new);
    }
    let o = rewrite_table.get(&computation.outputs[0]).unwrap().clone();
    ctx.assert(term![EQ; o, ctx.one().clone()]);
    computation.outputs = vec![term(AND, ctx.assertions)];
    for (value, name) in ctx.new_variables {
        computation.extend_precomputation(name, value);
    }
    computation
}
