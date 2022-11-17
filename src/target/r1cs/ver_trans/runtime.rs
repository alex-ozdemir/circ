use super::lang::{Ctx, Encoding, Pattern, Rule};
use crate::ir::term::*;
use circ_fields::FieldT;

use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::collections::BTreeSet;

use log::debug;

struct Rewriter<E: Encoding> {
    public_inputs: HashSet<String>,
    rules: HashMap<Pattern, Vec<Rule<E>>>,
    encs: HashMap<(Term, E::Type), E>,
    types: TermMap<BTreeSet<E::Type>>,
}

impl<E: Encoding> Rewriter<E> {
    fn new(public_inputs: HashSet<String>) -> Self {
        let mut rules_table: HashMap<Pattern, Vec<Rule<E>>> = HashMap::default();
        for r in E::rules() {
            let existing = rules_table.entry(*r.pattern()).or_insert_with(Vec::new);
            if existing.iter().find(|e_r| e_r.id == r.id).is_some() {
                panic!("Two rules for {:?}. Use different IDs.", r.pattern())
            }
            existing.push(r);
        }
        Self {
            public_inputs,
            rules: rules_table,
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
    fn assert(&mut self, c: &mut Ctx, t: Term) {
        match &t.op {
            Op::Eq => {
                let ty = self.get_max_ty(&t.cs[0]).max(self.get_max_ty(&t.cs[1]));
                self.ensure_enc(c, &t.cs[0], ty);
                self.ensure_enc(c, &t.cs[1], ty);
                self.get_enc(&t.cs[0], ty)
                    .assert_eq(c, self.get_enc(&t.cs[1], ty))
            }
            _ => {
                self.visit(c, t.clone());
                c.assert(self.get_enc(&t, self.get_max_ty(&t)).as_bool_term());
            }
        }
    }
    fn visit(&mut self, c: &mut Ctx, t: Term) {
        if self.types.get(&t).is_some() {
            return;
        }
        let new = if let Op::Var(name, sort) = &t.op {
            E::variable(c, name, sort, self.public_inputs.contains(name))
        } else if let Op::Const(_) = &t.op {
            let t_const = E::const_(c.field(), &t);
            // fold the constant encoding
            t_const.map(|t| {
                let c = crate::ir::opt::cfold::fold(&t, &[]);
                assert!(c.is_const(), "{:?} is not a constant", t);
                c
            })
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
                let id = E::choose(&t, &available);
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
            debug!("rule: op {}, first arg: {:?}", &t.op, r.encoding_ty(0));
            let res = r.apply(c, &t.op, &args);
            self.rules = rules_table;
            res
        };
        self.add(t, new);
    }
}

/// Apply some rules to translated a computation into a field.
pub fn apply_rules<E: Encoding>(field: FieldT, mut computation: Computation) -> Computation {
    assert!(computation.outputs.len() == 1);
    let o = computation.outputs[0].clone();
    let public_inputs = computation
        .metadata
        .public_input_names()
        .map(ToOwned::to_owned)
        .collect();
    // we're going to re-add all inputs.
    computation.metadata.computation_inputs.clear();
    let mut rewriter = Rewriter::<E>::new(public_inputs);
    let parents = extras::parents_map(&computation);
    let assertions: TermSet = match &o.op {
        &AND => o.cs.iter().cloned().collect(),
        _ => std::iter::once(o.clone()).collect(),
    };
    let mut do_not_embed = assertions.clone();
    if &o.op == &AND {
        do_not_embed.insert(o);
    }
    do_not_embed.retain(|c| parents.get(c).map(|ps| ps.len() <= 1).unwrap_or(true));
    let mut ctx = Ctx::new(field.clone());
    for t in computation.terms_postorder() {
        if !do_not_embed.contains(&t) {
            rewriter.visit(&mut ctx, t);
        }
    }
    for a in assertions {
        rewriter.assert(&mut ctx, a);
    }
    computation.outputs = vec![term(AND, ctx.assertions)];
    for (value, name, public) in ctx.new_variables {
        let vis = if public {
            None
        } else {
            Some(crate::ir::proof::PROVER_ID)
        };
        computation.extend_precomputation(name, value, Some(vis));
    }
    computation
}
