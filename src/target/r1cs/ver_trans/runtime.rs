use super::lang::{Chooser, Encoding, Pattern, Ctx, Rule};
use crate::ir::term::*;
use circ_fields::FieldT;

use fxhash::FxHashMap as HashMap;
use std::collections::BTreeSet;

struct Rewriter<E: Encoding> {
    rules: HashMap<Pattern, Vec<Rule<E>>>,
    chooser: Chooser<E::Type>,
    encs: HashMap<(Term, E::Type), E>,
    types: TermMap<BTreeSet<E::Type>>,
}

impl<E: Encoding> Rewriter<E> {
    fn new(rws: Vec<Rule<E>>, chooser: Chooser<E::Type>) -> Self {
        let mut rules_table: HashMap<Pattern, Vec<Rule<E>>> = HashMap::default();
        for r in rws {
            let existing = rules_table.entry(*r.pattern()).or_insert_with(Vec::new);
            if existing.iter().find(|e_r| e_r.id == r.id).is_some() {
                panic!("Two rules for {:?}. Use different IDs.", r.pattern())
            }
            existing.push(r);
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
    fn ensure_enc(&mut self, c: &mut Ctx, t: &Term, ty: E::Type) {
        if !self.encs.contains_key(&(t.clone(), ty)) {
            let from_ty = self.get_max_ty(t);
            let new_e = self.encs.get(&(t.clone(), from_ty)).unwrap().convert(c, ty);
            self.add(t.clone(), new_e);
        }
    }
    fn visit(&mut self, c: &mut Ctx, t: Term) {
        let new = if let Op::Var(name, sort) = &t.op {
            E::d_variable(c, name, sort)
        } else {
            let p = Pattern::from(&t);
            let rules_table = std::mem::take(&mut self.rules);
            let rules = rules_table
                .get(&p)
                .unwrap_or_else(|| panic!("No rule for pattern {:?}", p));
            let r = if rules.len() == 1 {
                &rules[0]
            } else {
                let available: Vec<&BTreeSet<E::Type>> =
                    t.cs.iter().map(|c| self.get_types(c)).collect();
                let id = (self.chooser)(&t, &available);
                rules
                    .iter()
                    .find(|r| r.id == id)
                    .unwrap_or_else(|| panic!("No rule for pattern {:?} has chosen id {}", p, id))
            };
            for (i, child) in t.cs.iter().enumerate() {
                self.ensure_enc(c, child, r.encoding_ty(i));
            }
            let args: Vec<&E> =
                t.cs.iter()
                    .enumerate()
                    .map(|(i, ch)| self.get_enc(ch, r.encoding_ty(i)))
                    .collect();
            let res = r.apply(c, &t.op, &args);
            self.rules = rules_table;
            res
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
    let mut ctx = Ctx::new(field.clone());
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
