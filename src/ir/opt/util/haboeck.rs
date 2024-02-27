//! Implementation of ROM checking based on https://eprint.iacr.org/2022/1530.pdf
//!
//! Cost: about (N + A)(L + 1) where the ROM size is N, there are A reads, and values have size L.
//! If the ROM contents are fixed, cost drops to N + A(L + 1)

use crate::front::PROVER_VIS;
use crate::ir::term::*;
use crate::util::ns::Namespace;

use log::debug;

/// The implementation of Haboeck's lookup argument.
///
/// Takes haystack, needles, and returns a term which should be asserted to ensure that each needle
/// is in haystack.
pub fn lookup(c: &mut Computation, ns: Namespace, haystack: Vec<Term>, needles: Vec<Term>) -> Term {
    debug!(
        "Haboeck lookup haystack {}, needles {}",
        haystack.len(),
        needles.len()
    );
    if haystack.is_empty() {
        assert!(needles.is_empty());
        return bool_lit(true);
    }
    let sort = check(&haystack[0]);
    let f = sort.as_pf().clone();
    let array_op = Op::Array(sort.clone(), sort.clone());
    let haystack_array = term(array_op.clone(), haystack.clone());
    let needles_array = term(array_op.clone(), needles.clone());
    let counts_pre = unmake_array(term![Op::ExtOp(ExtOp::Haboeck); haystack_array, needles_array]);
    let counts: Vec<Term> = counts_pre
        .into_iter()
        .enumerate()
        .map(|(i, coeff)| {
            c.new_var(
                &ns.fqn(format!("c{i}")),
                sort.clone(),
                PROVER_VIS,
                Some(coeff),
            )
        })
        .collect();
    let key = term(
        Op::PfChallenge(ns.fqn("key"), f.clone()),
        haystack
            .iter()
            .chain(&needles)
            .chain(&counts)
            .cloned()
            .collect(),
    );
    let haysum = term(
        PF_ADD,
        counts
            .into_iter()
            .zip(haystack)
            .map(|(ct, hay)| term![PF_DIV; ct, term![PF_ADD; hay, key.clone()]])
            .collect(),
    );
    let needlesum = term(
        PF_ADD,
        needles
            .into_iter()
            .map(|needle| term![PF_RECIP; term![PF_ADD; needle, key.clone()]])
            .collect(),
    );
    term![Op::Eq; haysum, needlesum]
}
