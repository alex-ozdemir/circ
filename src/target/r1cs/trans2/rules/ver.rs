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
                let all_bits = term(
                    AND,
                    fs.iter()
                        .map(|f| term![EQ; term![PF_MUL; f.clone(), f.clone()], f.clone()])
                        .collect(),
                );
                let sum = term(PF_ADD, fs.iter().enumerate().map(|(i, f)|
                        term![PF_MUL; pf_lit(field.new_v(Integer::from(1) << i)), f.clone()]).collect());
                let one = pf_lit(field.new_v(1));
                let zero = pf_lit(field.new_v(0));
                let sum2 = term(
                    PF_ADD,
                    (0..fs.len())
                        .map(|i| {
                            term![PF_MUL; pf_lit(field.new_v(Integer::from(1) << i)),
                            term![ITE; term![Op::BvBit(i); t.clone()], one.clone(), zero.clone()]]
                        })
                        .collect(),
                );
                term![AND; term![EQ; sum, sum2], all_bits]
            }
            Enc::Uint(f) => {
                let field = FieldT::from(check(f).as_pf());
                let n_bits = check(&t).as_bv();
                let sum2 = term(
                    PF_ADD,
                    (0..n_bits)
                        .map(|i| {
                            term![PF_MUL; pf_lit(field.new_v(Integer::from(1) << i)),
                            term![Op::BvBit(i); t.clone()]]
                        })
                        .collect(),
                );
                term![EQ; f.clone(), sum2]
            }
        }
    }
}
