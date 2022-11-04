use super::lang::{Chooser, Encoding, Pattern, RewriteCtx, Rule};
use crate::ir::term::*;
use circ_fields::FieldT;

use fxhash::FxHashMap as HashMap;
use std::collections::BTreeSet;

struct Rewriter<E: Encoding> {
    rules: HashMap<(Pattern, E::Type), Rule<E>>,
    chooser: Chooser<E::Type>,
    encs: HashMap<(Term, E::Type), E>,
    types: TermMap<BTreeSet<E::Type>>,
}

impl<E: Encoding> Rewriter<E> {
    fn new(rws: Vec<Rule<E>>, chooser: Chooser<E::Type>) -> Self {
        let mut rules_table: HashMap<(Pattern, E::Type), Rule<E>> = HashMap::default();
        for r in rws {
            let prev = rules_table.insert((r.pattern().clone(), r.encoding_ty()), r);
            if let Some(p) = prev {
                panic!("Two rules for {:?}", p.pattern())
            }
        }
        Self {
            rules: rules_table,
            chooser,
            encs: Default::default(),
            types: Default::default(),
        }
    }
    fn add(&mut self, t: Term, e: E) {
        let types = self.types.entry(t.clone()).or_default();
        if types.insert(e.type_()) {
            self.encs.insert((t, e.type_()), e);
        }
    }
    fn get_types(&self, t: &Term) -> &BTreeSet<E::Type> {
        self.types.get(t).unwrap()
    }
    fn get_max_ty(&self, t: &Term) -> E::Type {
        *self.get_types(t).iter().last().unwrap()
    }
    fn get_enc(&self, t: &Term, ty: E::Type) -> &E {
        self.encs.get(&(t.clone(), ty)).unwrap()
    }
    fn ensure_enc(&mut self, c: &mut RewriteCtx, t: &Term, ty: E::Type) {
        if !self.encs.contains_key(&(t.clone(), ty)) {
            let from_ty = self.get_max_ty(t);
            let new_e = self.encs.get(&(t.clone(), from_ty)).unwrap().convert(c, ty);
            self.add(t.clone(), new_e);
        }
    }
    fn visit(&mut self, c: &mut RewriteCtx, t: Term) {
        let new = if let Op::Var(name, sort) = &t.op {
            E::d_variable(c, name, sort)
        } else {
            let p = Pattern::from(&t);
            let available: Vec<&BTreeSet<E::Type>> =
                t.cs.iter().map(|c| self.get_types(c)).collect();
            let ty = (self.chooser)(&t, &available);
            for child in &t.cs {
                self.ensure_enc(c, child, ty);
            }
            let args: Vec<&E> = t.cs.iter().map(|ch| self.get_enc(ch, ty)).collect();
            let r = self
                .rules
                .get(&(p, ty))
                .unwrap_or_else(|| panic!("No pattern for pattern {:?} and encoding {:?}", p, ty));
            r.apply(c, &t.op, &args)
        };
        self.add(t, new);
    }
}

/// Apply some rules to translated a computation into a field.
pub fn apply_rules<E: Encoding>(
    rws: Vec<Rule<E>>,
    chooser: Chooser<E::Type>,
    field: FieldT,
    mut computation: Computation,
) -> Computation {
    assert!(computation.outputs.len() == 1);
    let mut rewriter = Rewriter::new(rws, chooser);
    let mut ctx = RewriteCtx::new(field.clone());
    for t in computation.terms_postorder() {
        rewriter.visit(&mut ctx, t);
    }
    let ty = rewriter.get_max_ty(&computation.outputs()[0]);
    let e = rewriter.get_enc(&computation.outputs()[0].clone(), ty);
    ctx.assert(e.as_bool_term());
    computation.outputs = vec![term(AND, ctx.assertions)];
    for (value, name) in ctx.new_variables {
        computation.extend_precomputation(name, value);
    }
    computation
}
