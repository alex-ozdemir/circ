//! Verification machinery
#![allow(unused_imports)]
use super::lang::{Ctx, Encoding, EncodingType, OpPat, Rule, SortPat};
use crate::ir::term::*;
use circ_fields::FieldT;
use fxhash::{FxHashMap, FxHashSet};
use std::collections::{BTreeSet, BinaryHeap};
use std::iter::repeat;

use Prop::*;

/// Terms that assert the precomputation for a [Ctx] was correct.
fn correct_precompute(c: &Ctx) -> Vec<Term> {
    c.new_variables
        .iter()
        .map(|(val, name, _)| {
            let var = leaf_term(Op::Var(name.into(), check(val)));
            term![EQ; var, val.clone()]
        })
        .collect()
}

/// Return the assertions of this [Ctx] with the precompute substituted in.
fn precompute_sub(c: &Ctx) -> Vec<Term> {
    let mut subs: TermMap<Term> = Default::default();
    for (val, name, _) in &c.new_variables {
        let val_s = extras::substitute_cache(&val, &mut subs);
        let sort = check(&val_s);
        let var = leaf_term(Op::Var(name.clone(), sort));
        assert!(subs.insert(var, val_s).is_none());
    }
    c.assertions
        .iter()
        .map(|a| extras::substitute_cache(a, &mut subs))
        .collect()
}

/// An encoding scheme with formalized semantics.
pub trait VerifiableEncoding: Encoding {
    /// Given a term `t` and encoded form `self`, return a boolean term which is true iff the
    /// encoding is valid.
    fn is_valid(&self, t: Term) -> Term;

    /// Sort patterns that this encoding might apply to
    fn sort_pats() -> BTreeSet<SortPat> {
        <Self::Type as EncodingType>::all()
            .into_iter()
            .map(|t| t.sort())
            .collect()
    }

    /// Sorts that this encoding might apply to (up to a bound)
    fn sorts(bnd: &Bound) -> Vec<Sort> {
        Self::sort_pats()
            .into_iter()
            .flat_map(|p| sorts(&p, bnd))
            .collect()
    }

    /// Create formulas that are SAT iff some variable rule is unsound.
    fn sound_vars(bnd: &Bound) -> Vec<VerCond> {
        Self::sorts(bnd)
            .into_iter()
            .map(|sort| {
                let mut ctx = Ctx::new(bnd.field.clone());
                let name = "a".to_owned();
                let e = Self::variable(&mut ctx, &name, &sort, false);
                let var = leaf_term(Op::Var(name.clone(), sort.clone()));
                let no_valid = term![NOT; term![Op::Quant(Quant {
                    ty: QuantType::Exists,
                    bindings: vec![(name, sort.clone())],
                }); e.is_valid(var)]];
                let mut assertions = ctx.assertions;
                assertions.push(no_valid);
                VerCond::new(Sound, RuleType::Var, mk_and(assertions)).sort(&sort)
            })
            .collect()
    }

    /// Create formulas that are SAT iff some variable rule is incomplete.
    fn complete_vars(bnd: &Bound) -> Vec<VerCond> {
        Self::sorts(bnd)
            .into_iter()
            .map(|sort| {
                let mut ctx = Ctx::new(bnd.field.clone());
                let name = "a".to_owned();
                let _e = Self::variable(&mut ctx, &name, &sort, false);
                let mut assertions = Vec::new();
                assertions.extend(correct_precompute(&ctx));
                assertions.push(term![NOT; mk_and(ctx.assertions)]);

                VerCond::new(Complete, RuleType::Conv, mk_and(assertions)).sort(&sort)
            })
            .collect()
    }

    /// List valid conversions
    fn valid_conversions(bnd: &Bound) -> Vec<(Self::Type, Self::Type, Sort)> {
        let mut out = Vec::new();
        for from in <Self::Type as EncodingType>::all() {
            for to in <Self::Type as EncodingType>::all() {
                if from != to && from.sort() == to.sort() {
                    for sort in sorts(&from.sort(), bnd) {
                        out.push((from, to, sort));
                    }
                }
            }
        }
        out
    }

    /// Create formulas that are SAT iff some conversion rule is unsound.
    fn sound_convs(bnd: &Bound) -> Vec<VerCond> {
        Self::valid_conversions(bnd)
            .into_iter()
            .map(|(from, to, sort)| {
                let mut ctx = Ctx::new(bnd.field.clone());
                let name = "a".to_owned();
                let e = Self::variable(&mut ctx, &name, &sort, false);
                let e_from = e.convert(&mut ctx, from);
                let var = leaf_term(Op::Var(name, sort.clone()));
                ctx.assertions.extend(correct_precompute(&ctx));
                let e2 = e_from.convert(&mut ctx, to);
                let is_valid = e2.is_valid(var);
                let mut assertions = ctx.assertions;
                assertions.push(term![NOT; is_valid]);
                VerCond::new(Sound, RuleType::Conv, mk_and(assertions))
                    .sort(&sort)
                    .from(from)
                    .to(to)
            })
            .collect()
    }

    /// Create formulas that are SAT iff some conversion rule is incomplete.
    fn complete_convs(bnd: &Bound) -> Vec<VerCond> {
        Self::valid_conversions(bnd)
            .into_iter()
            .map(|(from, to, sort)| {
                let mut ctx = Ctx::new(bnd.field.clone());
                let name = "a".to_owned();
                let e = Self::variable(&mut ctx, &name, &sort, false);
                let e_from = e.convert(&mut ctx, from);
                let _e2 = e_from.convert(&mut ctx, to);
                let mut assertions = Vec::new();
                assertions.extend(correct_precompute(&ctx));
                assertions.push(term![NOT; mk_and(ctx.assertions)]);
                VerCond::new(Complete, RuleType::Conv, mk_and(assertions))
                    .sort(&sort)
                    .from(from)
                    .to(to)
            })
            .collect()
    }

    /// List all configurations valid for this rule
    fn cfgs(rule: &Rule<Self>, bnd: &Bound) -> Vec<(Sort, Op, Vec<Sort>)> {
        let mut out = Vec::new();
        for sort in sorts(&rule.pattern().1, bnd) {
            for op in ops(&rule.pattern().0, &sort, bnd) {
                for arg_sorts in arg_sorts(&op, &sort, bnd) {
                    out.push((sort.clone(), op.clone(), arg_sorts))
                }
            }
        }
        out
    }

    /// Create formulas that are SAT iff some op rule is unsound.
    fn sound_ops(rule: &Rule<Self>, bnd: &Bound) -> Vec<VerCond> {
        Self::cfgs(rule, bnd)
            .into_iter()
            .map(|(sort, op, arg_sorts)| {
                let var_parts = gen_names(arg_sorts.clone());
                let mut assertions = Vec::new();

                // create inputs
                let args: Vec<Term> = var_parts
                    .iter()
                    .map(|(n, s)| leaf_term(Op::Var(n.clone(), s.clone())))
                    .collect();

                // validly encode them
                let mut ctx = Ctx::new(bnd.field.clone());
                let e_args: Vec<Self> = var_parts
                    .iter()
                    .zip(&args)
                    .enumerate()
                    .map(|(i, ((name, sort), b))| {
                        let e = Self::variable(&mut ctx, name, sort, false);
                        let e_from = e.convert(&mut ctx, rule.encoding_ty(i));
                        assertions.push(e_from.is_valid(b.clone()));
                        e_from
                    })
                    .collect();

                // apply the lowering rule
                let t = term(op.clone(), args.clone());
                let e_t = rule.apply(&mut ctx, &t.op, &e_args.iter().collect::<Vec<_>>());
                assertions.extend(ctx.assertions); // save the assertions

                // assert that the output is mal-encoded
                assertions.push(term![NOT; e_t.is_valid(t.clone())]);

                VerCond::new(Sound, RuleType::Op, mk_and(assertions))
                    .sort(&sort)
                    .op_pat(OpPat::from(&op))
                    .arg_sorts(&arg_sorts)
            })
            .collect()
    }

    /// Create formulas that are SAT iff some op rule is incomplete.
    fn complete_ops(rule: &Rule<Self>, bnd: &Bound) -> Vec<VerCond> {
        Self::cfgs(rule, bnd)
            .into_iter()
            .map(|(sort, op, arg_sorts)| {
                let var_parts = gen_names(arg_sorts.clone());
                let mut assertions = Vec::new();

                // create inputs
                let args: Vec<Term> = var_parts
                    .iter()
                    .map(|(n, s)| leaf_term(Op::Var(n.clone(), s.clone())))
                    .collect();

                // encode them
                let mut ctx = Ctx::new(bnd.field.clone());
                let e_args: Vec<Self> = var_parts
                    .iter()
                    .enumerate()
                    .map(|(i, (n, s))| {
                        let e = Self::variable(&mut ctx, n, s, false);
                        e.convert(&mut ctx, rule.encoding_ty(i))
                    })
                    .collect();

                // we check encodings separately
                ctx.assertions.clear();

                // apply the lowering rule
                let t = term(op.clone(), args.clone());
                let _e_t = rule.apply(&mut ctx, &t.op, &e_args.iter().collect::<Vec<_>>());

                // assert the pre-compute is correct, through substitution
                let ctx_assertions_subbed = precompute_sub(&ctx);

                // assert that some contraint is broken
                assertions.push(term![NOT; mk_and(ctx_assertions_subbed)]);

                VerCond::new(Complete, RuleType::Op, mk_and(assertions))
                    .sort(&sort)
                    .op_pat(OpPat::from(&op))
                    .arg_sorts(&arg_sorts)
            })
            .collect()
    }

    /// Create formulas that are SAT iff some const encoding rule is incorrect.
    fn correct_consts(bnd: &Bound) -> Vec<VerCond> {
        Self::sorts(bnd)
            .into_iter()
            .map(|sort| {
                let name = "a".to_owned();
                let var = leaf_term(Op::Var(name.clone(), sort.clone()));
                let e = Self::const_(&bnd.field, &var);
                VerCond::new(Complete, RuleType::Const, term![NOT; e.is_valid(var)]).sort(&sort)
            })
            .collect()
    }

    /// Generate ALL verification conditions
    fn all_vcs(bnd: &Bound) -> Vec<VerCond> {
        std::iter::empty()
            .chain(Self::correct_consts(bnd))
            .chain(Self::sound_vars(bnd))
            .chain(Self::complete_vars(bnd))
            .chain(Self::sound_convs(bnd))
            .chain(Self::complete_convs(bnd))
            .chain(Self::rules().iter().flat_map(|rule| {
                std::iter::empty()
                    .chain(Self::sound_ops(rule, bnd))
                    .chain(Self::complete_ops(rule, bnd))
            }))
            .map(VerCond::complete)
            .collect()
    }
}

/// The type of property
#[derive(Debug)]
pub enum Prop {
    /// A satisfiable output implies a satisfiable input.
    Sound,
    /// A satisfiable input implies a satisfiable output.
    Complete,
}

/// The type of rule
#[derive(Debug)]
pub enum RuleType {
    /// variable encoding
    Var,
    /// constant encoding
    Const,
    /// operator lowering
    Op,
    /// conversion
    Conv,
}

/// A bound for verification
pub struct Bound {
    /// The maximum number of operator arguments
    pub args: usize,
    /// The maximum size of bitvectors
    pub bv_bits: usize,
    /// The field
    pub field: FieldT,
}

/// Get all sorts for a [SortPat]
fn sorts(s: &SortPat, bnd: &Bound) -> Vec<Sort> {
    match s {
        SortPat::BitVector => (1..=bnd.bv_bits).map(Sort::BitVector).collect(),
        SortPat::Bool => vec![Sort::Bool],
        SortPat::Field => vec![Sort::Field(bnd.field.clone())],
    }
}

/// A verification condition
pub struct VerCond {
    /// key-value pairs that describe this VC
    pub tags: FxHashMap<String, String>,
    /// UNSAT if holds
    pub formula: Term,
}

const TAG_PROP: &str = "prop";
const TAG_TY: &str = "ty";
const TAG_SORT: &str = "sort";
const TAG_SORT_PAT: &str = "sort_pat";
const TAG_BV_BITS: &str = "bv_bits";
const TAG_ARG_SORTS: &str = "arg_sorts";
const TAG_N_ARGS: &str = "n_args";
const TAG_OP_PAT: &str = "op_pat";
const TAG_FROM: &str = "from";
const TAG_TO: &str = "to";

/// All tags
pub const TAGS: &[&str] = &[
    TAG_PROP,
    TAG_TY,
    TAG_SORT,
    TAG_SORT_PAT,
    TAG_BV_BITS,
    TAG_ARG_SORTS,
    TAG_N_ARGS,
    TAG_OP_PAT,
    TAG_FROM,
    TAG_TO,
];

impl VerCond {
    fn new(prop: Prop, ty: RuleType, formula: Term) -> Self {
        let this = Self {
            tags: Default::default(),
            formula,
        };
        this.tag(TAG_PROP, &format!("{:?}", prop))
            .tag(TAG_TY, &format!("{:?}", ty))
    }
    fn complete(mut self) -> Self {
        for t in TAGS {
            if !self.tags.contains_key(*t) {
                self = self.tag(t, &"");
            }
        }
        self
    }
    fn tag<T: AsRef<str>>(mut self, key: &str, val: &T) -> Self {
        assert!(self
            .tags
            .insert(key.to_lowercase(), val.as_ref().to_lowercase())
            .is_none());
        self
    }
    fn sort(self, sort: &Sort) -> Self {
        let w = match sort {
            Sort::BitVector(w) => *w,
            _ => 0,
        };
        self.tag(TAG_SORT, &format!("{}", sort))
            .tag(TAG_SORT_PAT, &format!("{}", SortPat::from(sort)))
            .tag(TAG_BV_BITS, &format!("{}", w))
    }
    fn arg_sorts(self, sorts: &[Sort]) -> Self {
        let mut s = String::new();
        for so in sorts {
            s += &format!("{}", so);
        }
        self.tag(TAG_ARG_SORTS, &s)
            .tag(TAG_N_ARGS, &format!("{}", sorts.len()))
    }
    fn op_pat(self, sort_pat: OpPat) -> Self {
        self.tag(TAG_OP_PAT, &format!("{}", sort_pat))
    }
    fn from<T: EncodingType>(self, ty: T) -> Self {
        self.tag(TAG_FROM, &format!("{:?}", ty))
    }
    fn to<T: EncodingType>(self, ty: T) -> Self {
        self.tag(TAG_TO, &format!("{:?}", ty))
    }
}

/// Return all (ordered) seqs of positive ints that sum to `sum`.
fn constant_sum_seqs(sum: usize) -> Vec<Vec<usize>> {
    if sum == 0 {
        vec![Vec::new()]
    } else {
        (1..=sum)
            .flat_map(|last| {
                constant_sum_seqs(sum - last)
                    .into_iter()
                    .map(move |mut chk| {
                        chk.push(last);
                        chk
                    })
            })
            .collect()
    }
}

/// Get all operators that would match this [Pattern].
fn ops(o: &OpPat, s: &Sort, bnd: &Bound) -> Vec<Op> {
    match o {
        OpPat::Eq => vec![Op::Eq],
        OpPat::Ite => vec![Op::Ite],
        OpPat::Not => vec![Op::Not],
        OpPat::BoolMaj => vec![Op::BoolMaj],
        OpPat::Implies => vec![Op::Implies],
        OpPat::BoolNaryOp(o) => vec![Op::BoolNaryOp(*o)],
        OpPat::PfUnOp(o) => vec![Op::PfUnOp(*o)],
        OpPat::PfNaryOp(o) => vec![Op::PfNaryOp(*o)],
        OpPat::BvBit => (0..s.as_bv()).map(|i| Op::BvBit(i)).collect(),
        OpPat::BvBinOp(o) => vec![Op::BvBinOp(*o)],
        OpPat::BvBinPred(o) => vec![Op::BvBinPred(*o)],
        OpPat::BvNaryOp(o) => vec![Op::BvNaryOp(*o)],
        OpPat::BvUnOp(o) => vec![Op::BvUnOp(*o)],
        OpPat::BoolToBv => vec![Op::BoolToBv],
        OpPat::BvExtract => (0..(bnd.bv_bits - s.as_bv()))
            .map(|l| Op::BvExtract(l + s.as_bv() - 1, l))
            .collect(),
        OpPat::BvConcat => vec![Op::BvConcat],
        OpPat::BvUext => (0..s.as_bv()).map(|i| Op::BvUext(i)).collect(),
        OpPat::BvSext => (0..s.as_bv()).map(|i| Op::BvSext(i)).collect(),
        OpPat::PfToBv => vec![Op::PfToBv(s.as_bv())],
        OpPat::UbvToPf => vec![Op::UbvToPf(s.as_pf().clone())],
    }
}

/// Get all argument sort sequences for a given operator
/// and sort parameter.
fn arg_sorts(o: &Op, s: &Sort, bnd: &Bound) -> Vec<Vec<Sort>> {
    match o {
        Op::Eq => vec![vec![s.clone(), s.clone()]],
        Op::Ite => vec![vec![Sort::Bool, s.clone(), s.clone()]],
        Op::BvUext(i) | Op::BvSext(i) => vec![vec![Sort::BitVector(s.as_bv() - i)]],
        Op::BoolToBv => vec![vec![Sort::Bool]],
        Op::PfToBv(_) => vec![vec![Sort::Field(bnd.field.clone())]],
        Op::UbvToPf(_) => (1..bnd.bv_bits).map(|i| vec![Sort::BitVector(i)]).collect(),
        Op::BvExtract(h, _) => (*h + 1..=bnd.bv_bits)
            .map(|w| vec![Sort::BitVector(w)])
            .collect(),
        Op::BvConcat => constant_sum_seqs(s.as_bv())
            .into_iter()
            .map(|sizes| sizes.into_iter().map(|s| Sort::BitVector(s)).collect())
            .collect(),
        _ => {
            if let Some(n_args) = o.arity() {
                vec![repeat(s).take(n_args).cloned().collect()]
            } else {
                (1..=bnd.args)
                    .map(|n| repeat(s).take(n).cloned().collect())
                    .collect()
            }
        }
    }
}

/// Generate names for some sorts
fn gen_names(sorts: Vec<Sort>) -> Vec<(String, Sort)> {
    fn nth_name(mut n: usize) -> String {
        let mut o = String::new();
        loop {
            o.push((b'a' + (n % 26) as u8) as char);
            n /= 26;
            if n == 0 {
                return o;
            }
        }
    }
    sorts
        .into_iter()
        .enumerate()
        .map(|(i, s)| (nth_name(i), s))
        .collect()
}

fn mk_and(mut ts: Vec<Term>) -> Term {
    match ts.len() {
        0 => bool_lit(true),
        1 => ts.pop().unwrap(),
        _ => term(AND, ts),
    }
}
