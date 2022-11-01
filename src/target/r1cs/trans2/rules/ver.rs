//! Verification shim for our rules.

use super::super::ver::VerifiableEncoding;
use super::Enc;
use crate::ir::term::*;

use circ_fields::FieldT;

impl VerifiableEncoding for Enc {
    fn is_valid(&self, t: Term) -> Term {
        match self {
            Enc::Bit(f) => {
                let field = FieldT::from(check(f).as_pf());
                let f_valid = term![EQ; term![PF_MUL; f.clone(), f.clone()], f.clone()];
                let f_is_1 = term![EQ; f.clone(), pf_lit(field.new_v(1))];
                term![AND; f_valid, term![EQ; t.clone(), f_is_1]]
            }
        }
    }
}
