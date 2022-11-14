//! Field IR (multiplication and addition only) to R1cs lowering

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
        let c = self.fresh_var("mul", mul_val, false);
        self.r1cs.constraint(a.1, b.1, c.1.clone());
        c
    }

    fn get(&self, t: &Term) -> TermLc {
        self.cache.get(t).unwrap().clone()
    }

    fn embed(&mut self, t: &Term) {
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
                let args = t.cs.iter().map(|c| self.get(c));
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
            Op::PfUnOp(PfUnOp::Neg) => Some(-self.get(&t.cs[0])),
            &AND => None,
            &EQ => {
                let diff = self.get(&t.cs[0]) - &self.get(&t.cs[1]);
                self.r1cs
                    .constraint(self.r1cs.zero(), self.r1cs.zero(), diff.1);
                None
            }
            o => panic!("invalid op in to_r1cs: {}", o),
        };
        if let Some(lc) = maybe_lc {
            self.cache.insert(t.clone(), lc);
        }
    }

    fn embed_all(&mut self, c: &Computation) {
        for t in c.terms_postorder() {
            if self.cache.contains_key(&t) {
                continue;
            }
            self.embed(&t);
        }
    }
}

/// Convert this (IR) constraint system `cs` to R1CS, over a prime field defined by `modulus`.
///
/// ## Returns
///
/// * The R1CS instance
pub fn to_r1cs(mut cs: Computation, modulus: FieldT) -> (R1cs<String>, ProverData, VerifierData) {
    cs.precomputes.recompute_inputs();
    if cs.outputs.len() > 1 {
        cs.outputs = vec![term(AND, cs.outputs)];
    }
    let mut cs = super::apply(&modulus, cs);
    cs.precomputes.recompute_inputs();
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
        converter.embed(&i);
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

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::util::field::DFL_T;

    use crate::ir::proof::Constraints;
    use crate::ir::term::dist::test::*;
    use crate::ir::term::dist::*;
    use crate::target::r1cs::opt::reduce_linearities;

    use circ_fields::FieldT;
    use fxhash::FxHashMap;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    use rand::distributions::Distribution;
    use rand::SeedableRng;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn bool() {
        init();
        let values: FxHashMap<String, Value> = vec![
            ("a".to_owned(), Value::Bool(true)),
            ("b".to_owned(), Value::Bool(false)),
        ]
        .into_iter()
        .collect();
        let cs = Computation::from_constraint_system_parts(
            vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
            ],
            vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                leaf_term(Op::Var("b".to_owned(), Sort::Bool)),
            ],
        );
        let (r1cs, pd, _) = to_r1cs(cs, FieldT::from(Integer::from(17)));
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }

    #[derive(Clone, Debug)]
    pub struct PureBool(pub Term, pub FxHashMap<String, Value>);

    impl Arbitrary for PureBool {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut rng = rand::rngs::StdRng::seed_from_u64(u64::arbitrary(g));
            let t = PureBoolDist(g.size()).sample(&mut rng);
            let values: FxHashMap<String, Value> = PostOrderIter::new(t.clone())
                .filter_map(|c| {
                    if let Op::Var(n, _) = &c.op {
                        Some((n.clone(), Value::Bool(bool::arbitrary(g))))
                    } else {
                        None
                    }
                })
                .collect();
            PureBool(t, values)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let vs = self.1.clone();
            let ts = PostOrderIter::new(self.0.clone())
                .collect::<Vec<_>>()
                .into_iter()
                .rev();

            Box::new(ts.skip(1).map(move |t| PureBool(t, vs.clone())))
        }
    }

    #[quickcheck]
    fn random_pure_bool(PureBool(t, values): PureBool) {
        let t = if eval(&t, &values).as_bool() {
            t
        } else {
            term![Op::Not; t]
        };
        let cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }

    #[quickcheck]
    fn random_bool(ArbitraryTermEnv(t, values): ArbitraryTermEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let mut cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        crate::ir::opt::scalarize_vars::scalarize_inputs(&mut cs);
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }

    #[quickcheck]
    fn random_pure_bool_opt(ArbitraryBoolEnv(t, values): ArbitraryBoolEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
        let r1cs2 = reduce_linearities(r1cs, None);
        r1cs2.check_all(&extended_values);
    }

    #[quickcheck]
    fn random_bool_opt(ArbitraryTermEnv(t, values): ArbitraryTermEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let mut cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        crate::ir::opt::scalarize_vars::scalarize_inputs(&mut cs);
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
        let r1cs2 = reduce_linearities(r1cs, None);
        r1cs2.check_all(&extended_values);
    }

    #[test]
    fn eq_test_simple() {
        init();
        const_test(term![
            Op::Eq;
            bv(0b0, 1),
            bv(0b0, 1)
        ]);
    }

    #[test]
    fn eq_test() {
        init();
        let values = vec![(
            "b".to_owned(),
            Value::BitVector(BitVector::new(Integer::from(152), 8)),
        )]
        .into_iter()
        .collect();

        let cs = Computation::from_constraint_system_parts(
            vec![term![Op::Not; term![Op::Eq; bv(0b10110, 8),
                              term![Op::BvUnOp(BvUnOp::Neg); leaf_term(Op::Var("b".to_owned(), Sort::BitVector(8)))]]]],
            vec![leaf_term(Op::Var("b".to_owned(), Sort::BitVector(8)))],
        );
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }

    #[test]
    fn not_opt_test() {
        init();
        let t = term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))];
        let values: FxHashMap<String, Value> = vec![("b".to_owned(), Value::Bool(true))]
            .into_iter()
            .collect();
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let cs = Computation::from_constraint_system_parts(vec![t], vec![]);
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
        let r1cs2 = reduce_linearities(r1cs, None);
        r1cs2.check_all(&extended_values);
    }

    /// A bit-vector literal with value `u` and size `w`
    pub fn bv(u: usize, w: usize) -> Term {
        leaf_term(Op::Const(Value::BitVector(BitVector::new(
            Integer::from(u),
            w,
        ))))
    }

    fn pf(i: isize) -> Term {
        leaf_term(Op::Const(Value::Field(DFL_T.new_v(i))))
    }

    fn const_test(term: Term) {
        let mut cs = Computation::new();
        cs.assert(term);
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&Default::default());
        r1cs.check_all(&extended_values);
    }

    #[test]
    fn div_test() {
        init();
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv(0b1111,4), bv(0b1111,4)],
            bv(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv(0b1111,4), bv(0b0001,4)],
            bv(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv(0b0111,4), bv(0b0000,4)],
            bv(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv(0b1111,4), bv(0b0010,4)],
            bv(0b0111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv(0b1111,4), bv(0b1111,4)],
            bv(0b0000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv(0b1111,4), bv(0b0001,4)],
            bv(0b0000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv(0b0111,4), bv(0b0000,4)],
            bv(0b0111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv(0b1111,4), bv(0b0010,4)],
            bv(0b0001, 4)
        ]);
    }

    #[test]
    fn sh_test() {
        init();
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Shl); bv(0b1111,4), bv(0b0011,4)],
            bv(0b1000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Shl); bv(0b1101,4), bv(0b0010,4)],
            bv(0b0100, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Ashr); bv(0b1111,4), bv(0b0011,4)],
            bv(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Ashr); bv(0b0111,4), bv(0b0010,4)],
            bv(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Lshr); bv(0b0111,4), bv(0b0010,4)],
            bv(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Lshr); bv(0b1111,4), bv(0b0011,4)],
            bv(0b0001, 4)
        ]);
    }

    #[test]
    fn pf2bv() {
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(4); pf(8)],
            bv(0b1000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(4); pf(15)],
            bv(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(8); pf(15)],
            bv(0b1111, 8)
        ]);
    }

    #[test]
    fn tuple() {
        let values = vec![
            ("a".to_owned(), Value::Bool(true)),
            ("b".to_owned(), Value::Bool(false)),
        ]
        .into_iter()
        .collect();
        let mut cs = Computation::from_constraint_system_parts(
            vec![
                term![Op::Field(0); term![Op::Tuple; leaf_term(Op::Var("a".to_owned(), Sort::Bool)), leaf_term(Op::Const(Value::Bool(false)))]],
                term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
            ],
            vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                leaf_term(Op::Var("b".to_owned(), Sort::Bool)),
            ],
        );
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let (r1cs, pd, _) = to_r1cs(cs, FieldT::from(Integer::from(17)));
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }
}
