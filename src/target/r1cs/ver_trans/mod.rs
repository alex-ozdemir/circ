//! IR -> R1CS

use crate::ir::term::Computation;
use circ_fields::FieldT;

pub mod ast;
pub mod lang;
pub mod rules;
mod runtime;
pub mod ver;

/// Lower
pub fn apply(field: &FieldT, computation: Computation) -> Computation {
    runtime::apply_rules(
        rules::rules(),
        Box::new(rules::choose),
        field.clone(),
        computation,
    )
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::proof::Constraints;
    use crate::ir::term::*;
    use crate::target::r1cs::trans::test::PureBool;
    use crate::util::field::DFL_T;
    use quickcheck_macros::quickcheck;

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
           format!("
            (computation
                (metadata () () ())
                {}
            )
        ", b).as_bytes(),
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
    fn bv_neg() {
        const_test("(not ((bit 0) (bvneg #b000)))");
        const_test("(not ((bit 0) (bvneg #b010)))");
    }
}
