//! IR -> R1CS

use crate::ir::term::Computation;
use crate::ir::term::*;
//use crate::ir::opt::{cfold::fold, flat::flatten_nary_ops};
use crate::target::r1cs::{ProverData, R1cs, VerifierData};

use circ_fields::FieldT;

use log::trace;

pub mod ast;
pub mod lang;
pub mod rules;
mod runtime;
mod to_r1cs;
pub mod ver;

#[cfg(test)]
mod test;

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
    trace!("Pre-lower: {}", text::pp_sexpr(format!("{}", cs.metadata).as_bytes(), 120));
    let mut cs = apply(&modulus, cs);
    //cs.outputs[0] = fold(&flatten_nary_ops(fold(&cs.outputs[0], &[])), &[]);
    trace!("Post-lower: {}", text::pp_sexpr(text::serialize_term(&cs.outputs()[0]).as_bytes(), 120));
    cs.precomputes.recompute_inputs();
    to_r1cs::to_r1cs(cs, modulus)
}
