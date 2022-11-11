//! Verification shim for our rules.

use super::super::ver::VerifiableEncoding;
use super::Enc;
use crate::ir::term::*;

use circ_fields::FieldT;

use rug::Integer;

impl VerifiableEncoding for Enc {
    fn is_valid(&self, t: Term) -> Term {
        match self {
            Enc::Bit(f) => {
                let field = FieldT::from(check(f).as_pf());
                let f_valid = term![EQ; term![PF_MUL; f.clone(), f.clone()], f.clone()];
                let f_is_1 = term![EQ; f.clone(), pf_lit(field.new_v(1))];
                term![AND; f_valid, term![EQ; t.clone(), f_is_1]]
            }
            Enc::Bits(fs) => {
                let field = FieldT::from(check(&fs[0]).as_pf());
                let one = pf_lit(field.new_v(1));
                let zero = pf_lit(field.new_v(0));
                term(
                    AND,
                    fs.iter()
                        .enumerate()
                        .map(|(i, f)| {
                            let is1 = term![EQ; term![Op::BvExtract(i,i); t.clone()], bv_lit(1,1)];
                            term![EQ; term![ITE; is1, one.clone(), zero.clone()], f.clone()]
                        })
                        .collect(),
                )
            }
            Enc::Uint(f, _) => {
                let field = FieldT::from(check(f).as_pf());
                let n_bits = check(&t).as_bv();
                let one = pf_lit(field.new_v(1));
                let zero = pf_lit(field.new_v(0));
                let sum2 = term(
                    PF_ADD,
                    (0..n_bits)
                        .map(|i| {
                            term![PF_MUL; pf_lit(field.new_v(Integer::from(1) << i)),
                            term![ITE; term![Op::BvBit(i); t.clone()], one.clone(), zero.clone()]]
                        })
                        .collect(),
                );
                term![EQ; f.clone(), sum2]
            }
            Enc::Field(f) => term![EQ; f.clone(), t],
        }
    }
}
