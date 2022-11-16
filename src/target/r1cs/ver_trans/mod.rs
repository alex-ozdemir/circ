//! IR -> R1CS

use crate::ir::term::Computation;
use crate::ir::term::*;
use crate::target::r1cs::{ProverData, R1cs, VerifierData};

use circ_fields::FieldT;

use log::trace;

pub mod ast;
pub mod lang;
pub mod rules;
mod runtime;
mod to_r1cs;
pub mod ver;

/// Lower
pub fn apply(field: &FieldT, computation: Computation) -> Computation {
    runtime::apply_rules::<rules::Enc>(field.clone(), computation)
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
    trace!("Pre-lower: {}", text::pp_sexpr(text::serialize_term(&cs.outputs()[0]).as_bytes(), 120));
    let mut cs = apply(&modulus, cs);
    trace!("Post-lower: {}", text::pp_sexpr(text::serialize_term(&cs.outputs()[0]).as_bytes(), 120));
    cs.precomputes.recompute_inputs();
    to_r1cs::to_r1cs(cs, modulus)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::proof::Constraints;
    use crate::ir::term::dist::test::ArbitraryTermEnv;
    use crate::ir::term::*;
    use crate::target::r1cs::trans::test::PureBool;
    use crate::util::field::DFL_T;
    use quickcheck_macros::quickcheck;
    use rug::Integer;

    #[test]
    fn simple() {
        let _ = env_logger::builder().is_test(true).try_init();
        let cs = text::parse_computation(
            b"
            (computation
                (metadata
                    (P V)
                    ((a bool) (b bool) (c bool))
                    ((a P) (b P))
                )
                (precompute () () (#t))
                (= (xor a b) c)
            )
        ",
        );
        let values = text::parse_value_map(
            b"
        (let (
          (a true)
          (b true)
          (c false)
          ) true ; dead
        )
        ",
        );
        assert_eq!(vec![Value::Bool(true)], cs.eval(&values));
        let cs2 = apply(&FieldT::FBls12381, cs);
        assert_eq!(vec![Value::Bool(true)], cs2.eval(&values));
    }

    #[test]
    fn all_ops() {
        let _ = env_logger::builder().is_test(true).try_init();
        let cs = text::parse_computation(
            b"
            (computation
                (metadata
                    (P V)
                    ((a bool) (b0 bool) (b1 bool) (b2 bool) (c bool) (d bool))
                    ((a P) (b P))
                )
                (precompute () () (#t))
                (= (xor a (and b0 b1 b2)) (=> c (or (not d) (not d))))
            )
        ",
        );
        let values = text::parse_value_map(
            b"
        (let (
          (a true)
          (b0 true)
          (b1 true)
          (b2 true)
          (c true)
          (d true)
          ) true ; dead
        )
        ",
        );
        assert_eq!(vec![Value::Bool(true)], cs.eval(&values));
        let cs2 = apply(&FieldT::FBls12381, cs);
        assert_eq!(vec![Value::Bool(true)], cs2.eval(&values));
    }

    #[track_caller]
    fn const_test(b: &str) {
        let _ = env_logger::builder().is_test(true).try_init();
        let cs = text::parse_computation(
            format!(
                "
            (computation
                (metadata () () ())
                (precompute () () (#t))
                {}
            )
        ",
                b
            )
            .as_bytes(),
        );
        let values = text::parse_value_map(
            b"
        (let (
          ) true ; dead
        )
        ",
        );
        assert_eq!(vec![Value::Bool(true)], cs.eval(&values));
        let cs2 = apply(&DFL_T, cs);
        assert_eq!(vec![Value::Bool(true)], cs2.eval(&values));
    }

    #[test]
    fn or3false() {
        const_test("(not (or false false false))");
    }

    #[test]
    fn impl_tf() {
        const_test("(not (=> true false))")
    }

    #[quickcheck]
    fn random_pure_bool(PureBool(t, values): PureBool) {
        let t = if eval(&t, &values).as_bool() {
            t
        } else {
            term![Op::Not; t]
        };
        let cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        assert_eq!(vec![Value::Bool(true)], cs.eval(&values));
        let cs2 = apply(&DFL_T, cs);
        assert_eq!(vec![Value::Bool(true)], cs2.eval(&values));
    }

    #[test]
    fn maj_ttf() {
        const_test("(maj true true false)")
    }

    #[test]
    fn bv_bit() {
        const_test("((bit 3) #b10001000)")
    }

    #[test]
    fn bv_not() {
        const_test("((bit 0) (bvnot #b110))")
    }

    #[test]
    fn bv_ite() {
        const_test("((bit 0) (ite true #b111 #b010))")
    }

    #[test]
    fn bv_cmp() {
        let w = 2;
        for l in 0..(1 << w) {
            for r in 0..(1 << w) {
                for o in &[
                    BV_UGE, BV_UGT, BV_ULE, BV_ULT, BV_SGE, BV_SGT, BV_SLE, BV_SLT, EQ,
                ] {
                    let t = term![o.clone(); bv_lit(l, w), bv_lit(r, w)];
                    let output = eval(&t, &Default::default()).as_bool();
                    let tt = if output { t } else { term![NOT; t] };
                    let s = format!("{}", tt);
                    const_test(&s);
                }
                for o in &[BV_UREM, BV_UDIV, BV_SUB] {
                    let t = term![o.clone(); bv_lit(l, w), bv_lit(r, w)];
                    let output = eval(&t, &Default::default());
                    let tt = term![EQ; leaf_term(Op::Const(output)), t];
                    let s = format!("{}", tt);
                    const_test(&s);
                }
            }
        }
    }

    #[test]
    fn bv_udiv_zero() {
        const_test("((bit 0) (bvudiv #b001 #b000))")
    }

    #[test]
    fn bv_neg() {
        const_test("(not ((bit 0) (bvneg #b000)))");
        const_test("(not ((bit 0) (bvneg #b010)))");
    }

    #[test]
    fn complex() {
        let _ = env_logger::builder().is_test(true).try_init();
        let cs = text::parse_computation(
            b"
            (computation
                (metadata
                    (P V)
                    ((a bool) (b bool) (c bool) (d (bv 4)) (e (mod 17)) (f (bv 5)))
                    ((a P) (b P))
                )
                (precompute () () (#t))
                (and
                  a
                  (not (xor a b))
                  (= a (not c))
                  (= a (not ((bit 0) d)))
                  (= a (not ((bit 0) (bvadd d d))))
                  (= a (not ((bit 0) (bvmul d d))))
                  (= a ((bit 0) (bvudiv #b0 #b0)))
                  (= a ((bit 0) (bvudiv d d)))
                  (= (* e e) e)
                  (= d ((extract 4 1) f))
                )
            )
        ",
        );
        let values = text::parse_value_map(
            b"
        (let (
          (a true)
          (b true)
          (c false)
          (d #b0000)
          (e #f1m17)
          (f #b00001)
          ) true ; dead
        )
        ",
        );
        assert_eq!(vec![Value::Bool(true)], cs.eval(&values));
        let cs2 = apply(&FieldT::from(Integer::from(17)), cs);
        assert_eq!(vec![Value::Bool(true)], cs2.eval(&values));
    }

    #[quickcheck]
    fn random_bool_opt(ArbitraryTermEnv(t, values): ArbitraryTermEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let mut cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        assert_eq!(vec![Value::Bool(true)], cs.eval(&values));
        crate::ir::opt::scalarize_vars::scalarize_inputs(&mut cs);
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        assert_eq!(vec![Value::Bool(true)], cs.eval(&values));
        let cs2 = apply(&DFL_T, cs);
        assert_eq!(vec![Value::Bool(true)], cs2.eval(&values));
    }

    mod to_r1cs {

        use super::super::to_r1cs;
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
}
