//! Field IR (multiplication, addition, and negation only) to R1cs lowering

use crate::ir::term::precomp::PreComp;
use crate::ir::term::*;
use crate::target::r1cs::*;

use circ_fields::FieldT;

use fxhash::FxHashSet;

use log::debug;

struct ToR1cs {
    r1cs: R1cs<String>,
    cache: TermMap<TermLc>,
    wit_ext: PreComp,
    public_inputs: FxHashSet<String>,
    next_idx: usize,
    zero: TermLc,
    to_bit_constrain: Vec<Term>,
    to_assert_eq: Vec<Term>,
    to_assert: Vec<Term>,
    to_embed: Vec<Term>,
}

impl ToR1cs {
    fn new(field: FieldT, precompute: precomp::PreComp, public_inputs: FxHashSet<String>) -> Self {
        debug!("Starting R1CS back-end, field: {}", field);
        let r1cs = R1cs::new(field.clone());
        let zero = TermLc(pf_lit(field.new_v(0u8)), r1cs.zero());
        Self {
            r1cs,
            cache: TermMap::new(),
            wit_ext: precompute,
            public_inputs,
            next_idx: 0,
            zero,
            to_bit_constrain: Vec::new(),
            to_assert_eq: Vec::new(),
            to_assert: Vec::new(),
            to_embed: Vec::new(),
        }
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    ///
    /// `comp` is a term that computes the value.
    fn fresh_var(&mut self, ctx: &str, comp: Term, public: bool) -> TermLc {
        let n = format!("{}_n{}", ctx, self.next_idx);
        self.next_idx += 1;
        debug_assert!(matches!(check(&comp), Sort::Field(_)));
        self.r1cs.add_signal(n.clone(), comp.clone());
        self.wit_ext.add_output(n.clone(), comp.clone());
        if public {
            self.r1cs.publicize(&n);
        }
        debug!("fresh: {}", n);
        TermLc(comp, self.r1cs.signal_lc(&n))
    }

    /// Return the product of `a` and `b`.
    fn mul(&mut self, a: TermLc, b: TermLc) -> TermLc {
        let mul_val = term![PF_MUL; a.0, b.0];
        if let Some(c) = a.1.as_const() {
            TermLc(mul_val, b.1 * c)
        } else if let Some(c) = b.1.as_const() {
            TermLc(mul_val, a.1 * c)
        } else {
            let c = self.fresh_var("mul", mul_val, false);
            self.r1cs.constraint(a.1, b.1, c.1.clone());
            c
        }
    }

    fn get(&self, t: &Term) -> &TermLc {
        self.cache.get(t).unwrap()
    }

    fn embed(&mut self, t: Term) {
        if self.cache.contains_key(&t) {
            return
        }
        let maybe_lc = match &t.op {
            Op::Var(name, Sort::Field(_)) => {
                let public = self.public_inputs.contains(name);
                Some(self.fresh_var(name, t.clone(), public))
            }
            Op::Const(Value::Field(r)) => Some(TermLc(
                t.clone(),
                self.r1cs.constant(r.as_ty_ref(&self.r1cs.modulus)),
            )),
            Op::PfNaryOp(o) => {
                let args = t.cs.iter().map(|c| self.get(c).clone());
                Some(match o {
                    PfNaryOp::Add => args.fold(self.zero.clone(), |a, b| a + &b),
                    PfNaryOp::Mul => {
                        // Needed to end the above closures borrow of self, before the mul call
                        #[allow(clippy::needless_collect)]
                        let args = args.collect::<Vec<_>>();
                        let mut args_iter = args.into_iter();
                        let first = args_iter.next().unwrap();
                        args_iter.fold(first, |a, b| self.mul(a, b))
                    }
                })
            }
            Op::PfUnOp(PfUnOp::Neg) => Some(-self.get(&t.cs[0]).clone()),
            o => panic!("invalid op in to_r1cs: {}", o),
        };
        if let Some(lc) = maybe_lc {
            self.cache.insert(t, lc);
        }
    }

    fn collect_assertions(&mut self, t: &Term) {
        match &t.op {
            &AND => t.cs.iter().for_each(|c| self.collect_assertions(c)),
            &EQ => {
                if t.cs[0].op == PF_MUL
                    && t.cs[0].cs[0] == t.cs[0].cs[1]
                    && t.cs[0].cs[1] == t.cs[1]
                {
                    // bit-constraint case
                    self.to_embed.push(t.cs[1].clone());
                    self.to_bit_constrain.push(t.cs[1].clone());
                } else {
                    self.to_embed.extend(t.cs.iter().cloned());
                    self.to_assert_eq.push(t.clone());
                }
            }
            _ => {
                self.to_embed.push(t.clone());
                self.to_assert.push(t.clone());
            }
        }
    }

    fn embed_all(&mut self, c: &Computation) {
        debug_assert_eq!(c.outputs().len(), 1);
        self.collect_assertions(&c.outputs()[0]);
        let to_embed = std::mem::take(&mut self.to_embed);
        for t in PostOrderIter::from_iter(to_embed.into_iter()) {
            self.embed(t);
        }
        for b in std::mem::take(&mut self.to_bit_constrain).into_iter() {
            let lc = self.get(&b).1.clone();
            let lc_sub1 = lc.clone() - &self.r1cs.modulus.new_v(1);
            self.r1cs
                .constraint(lc.clone(), lc_sub1, self.zero.1.clone());
        }
        for a in std::mem::take(&mut self.to_assert_eq).into_iter() {
            debug_assert_eq!(a.op, EQ);
            let d = self.get(&a.cs[0]).1.clone() - &self.get(&a.cs[1]).1;
            self.r1cs.constraint(self.r1cs.zero(), self.r1cs.zero(), d);
        }
        for a in std::mem::take(&mut self.to_assert).into_iter() {
            let d = self.get(&a.cs[0]).1.clone() - &self.r1cs.modulus.new_v(1);
            self.r1cs.constraint(self.r1cs.zero(), self.r1cs.zero(), d);
        }
    }
}

/// Convert this (IR) constraint system `cs` to R1CS, over a prime field defined by `modulus`.
///
/// ## Returns
///
/// * The R1CS instance
pub fn to_r1cs(mut cs: Computation, modulus: FieldT) -> (R1cs<String>, ProverData, VerifierData) {
    let metadata = cs.metadata.clone();
    let public_inputs = metadata
        .public_input_names()
        .map(ToOwned::to_owned)
        .collect();
    debug!("public inputs: {:?}", public_inputs);
    debug!("Term count: {}", cs.terms_postorder().count(),);
    let mut converter = ToR1cs::new(modulus, cs.precomputes.clone(), public_inputs);
    debug!("declaring inputs");
    for i in metadata.public_inputs() {
        debug!("input {}", i);
        converter.embed(i);
    }
    debug!("Printing assertions");
    converter.embed_all(&cs);
    debug!("r1cs public inputs: {:?}", converter.r1cs.public_idxs,);
    cs.precomputes = converter.wit_ext;
    let r1cs = converter.r1cs;
    let prover_data = r1cs.prover_data(&cs);
    let verifier_data = r1cs.verifier_data(&cs);
    (r1cs, prover_data, verifier_data)
}
