use super::lang::{Chooser, Conversion, Encoding, Pattern, RewriteCtx, Rule};
use crate::ir::term::*;
use circ_fields::FieldT;

use fxhash::FxHashMap as HashMap;
use std::collections::BTreeSet;

struct Rewriter<E: Encoding> {
    rules: HashMap<(Pattern, E::Type), Rule<E>>,
    convs: HashMap<(E::Type, E::Type), Conversion<E>>,
    chooser: Chooser<E::Type>,
    encs: HashMap<(Term, E::Type), E>,
    types: TermMap<BTreeSet<E::Type>>,
}

impl<E: Encoding> Rewriter<E> {
    fn new(rws: Vec<Rule<E>>, convs: Vec<Conversion<E>>, chooser: Chooser<E::Type>) -> Self {
        let mut rules_table: HashMap<(Pattern, E::Type), Rule<E>> = HashMap::default();
        for r in rws {
            let prev = rules_table.insert((r.pattern().clone(), r.encoding_ty()), r);
            if let Some(p) = prev {
                panic!("Two rules for {:?}", p.pattern())
            }
        }
        let mut convs_table: HashMap<(E::Type, E::Type), Conversion<E>> = Default::default();
        for c in convs {
            let from = c.from();
            let to = c.to();
            let prev = convs_table.insert((from, to), c);
            if prev.is_some() {
                panic!("Two conversion rules for {:?} -> {:?}", from, to);
            }
        }
        Self {
            rules: rules_table,
            convs: convs_table,
            chooser,
            encs: Default::default(),
            types: Default::default(),
        }
    }
    fn add(&mut self, t: Term, e: E) {
        dbg!(&t);
        dbg!(&e);
        let types = self.types.entry(t.clone()).or_default();
        if types.insert(e.type_()) {
            self.encs.insert((t, e.type_()), e);
        }
    }
    #[track_caller]
    fn get_types(&self, t: &Term) -> &BTreeSet<E::Type> {
        self.types
            .get(t)
            .unwrap_or_else(|| panic!("*No* encoding for term"))
    }
    fn get_max_ty(&self, t: &Term) -> E::Type {
        *self
            .get_types(t)
            .iter()
            .last()
            .unwrap_or_else(|| panic!("*No* encoding for term"))
    }
    fn get_enc(&self, t: &Term, ty: E::Type) -> &E {
        self.encs.get(&(t.clone(), ty)).unwrap()
    }
    fn ensure_enc(&mut self, c: &mut RewriteCtx, t: &Term, ty: E::Type) {
        if !self.encs.contains_key(&(t.clone(), ty)) {
            let from_ty = self.get_max_ty(t);
            let cnv = self
                .convs
                .get(&(from_ty, ty))
                .unwrap_or_else(|| panic!("No conversion {:?} -> {:?}", from_ty, ty));
            let e = self.encs.get(&(t.clone(), from_ty)).unwrap();
            let new_e = cnv.apply(c, e);
            self.add(t.clone(), new_e);
        }
    }
    fn visit(&mut self, c: &mut RewriteCtx, t: Term) {
        let new = if let Op::Var(name, sort) = &t.op {
            E::variable(c, name, sort)
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
    convs: Vec<Conversion<E>>,
    chooser: Chooser<E::Type>,
    field: FieldT,
    mut computation: Computation,
) -> Computation {
    assert!(computation.outputs.len() == 1);
    let mut rewriter = Rewriter::new(rws, convs, chooser);
    let mut ctx = RewriteCtx::new(field.clone());
    for t in computation.terms_postorder() {
        rewriter.visit(&mut ctx, t);
    }
    let ty = rewriter.get_max_ty(&computation.outputs()[0]);
    let e = rewriter
        .encs
        .get(&(computation.outputs()[0].clone(), ty))
        .unwrap();
    ctx.assert(e.as_bool_term());
    computation.outputs = vec![term(AND, ctx.assertions)];
    for (value, name) in ctx.new_variables {
        computation.extend_precomputation(name, value);
    }
    computation
}
