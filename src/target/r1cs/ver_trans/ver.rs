//! Verification machinery
use super::lang::{Ctx, Encoding, EncodingType, OpPat, Rule, SortPat};
use crate::ir::term::*;
use circ_fields::FieldT;
use fxhash::FxHashMap;
use std::collections::BTreeSet;
use std::iter::repeat;
use std::marker::PhantomData;
use std::mem::take;

use Prop::*;

struct Builder<E> {
    ctx: Ctx,
    subs: TermMap<Term>,
    _phant: PhantomData<E>,
}

impl<E: VerifiableEncoding> Builder<E> {
    fn new(bnd: &Bound) -> Self {
        Self {
            ctx: Ctx::new(bnd.field.clone()),
            subs: Default::default(),
            _phant: Default::default(),
        }
    }

    /// Encode a new variable `(name, sort)` as `ty`. Pass `public` through.
    ///
    /// If no `ty` is given, the default is used.
    ///
    /// Returns (encoding, var term, is valid, assertions)
    fn new_enc(
        &mut self,
        name: &str,
        sort: &Sort,
        ty: Option<E::Type>,
        public: bool,
    ) -> (E, Term, Term, Term) {
        assert!(self.ctx.assertions.is_empty());
        let mut e = E::variable(&mut self.ctx, name, sort, public);
        let var = leaf_term(Op::Var(name.into(), sort.clone()));
        if let Some(ty) = ty {
            e = e.convert(&mut self.ctx, ty);
        }
        let is_valid = e.is_valid(var.clone());
        (e, var, is_valid, mk_and(take(&mut self.ctx.assertions)))
    }

    /// Create an term and encoding that is structurally guaranteed to be valid for it.
    fn valid_enc(&mut self, name: &str, sort: &Sort, ty: E::Type) -> (E, Term) {
        let var = leaf_term(Op::Var(name.into(), sort.clone()));
        (E::from_term(var.clone(), ty, self.ctx.field()), var)
    }

    /// Capture the assertions for contextual code
    fn capture<T, F: FnOnce(&mut Ctx) -> T>(&mut self, f: F) -> (Term, T) {
        assert!(self.ctx.assertions.is_empty());
        let t = f(&mut self.ctx);
        (mk_and(take(&mut self.ctx.assertions)), t)
    }

    /// Substitute correct precomputation into this term.
    fn sub(&mut self, t: &Term) -> Term {
        for (val, name, _) in take(&mut self.ctx.new_variables) {
            let val_s = extras::substitute_cache(&val, &mut self.subs);
            let sort = check(&val_s);
            let var = leaf_term(Op::Var(name.clone(), sort));
            assert!(self.subs.insert(var, val_s).is_none());
        }
        extras::substitute_cache(t, &mut self.subs)
    }
}

/// An encoding scheme with formalized semantics.
pub trait VerifiableEncoding: Encoding {
    /// Create an encoding with fresh variables begining with `prefix`.
    fn floating(prefix: &str, ty: Self::Type, f: &FieldT, s: &Sort) -> Self;

    /// Given a term `t` and encoded form `self`, return a boolean term which is true iff the
    /// encoding is valid.
    fn is_valid(&self, t: Term) -> Term;

    /// Give the (unique) valid encoding of this term.
    ///
    /// We'll generate VCs to test uniqueness.
    fn from_term(t: Term, ty: Self::Type, f: &FieldT) -> Self;

    /// Are these two encodings equal?
    fn eq(&self, other: &Self) -> Term {
        term(
            AND,
            self.terms()
                .into_iter()
                .zip(other.terms())
                .map(|(s, o)| term![EQ; s, o])
                .collect(),
        )
    }

    /// Give the (unique) term this valid encoding is for.
    ///
    /// We'll generate VCs to test uniqueness.
    fn to_term(&self) -> Term;

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
    fn var_vcs(bnd: &Bound) -> Vec<Vc> {
        let mut vcs = Vec::new();
        for sort in Self::sorts(bnd) {
            for public in [false, true] {
                for prop in [Sound, Complete] {
                    if !(prop == Sound && public) {
                        let mut b = Builder::<Self>::new(&bnd);
                        let name = "a".to_owned();
                        let (_, _, valid, sat) = b.new_enc(&name, &sort, None, public);
                        let condition = if prop.trust() {
                            b.sub(&term![AND; valid, sat])
                        } else {
                            let some_valid = term![Op::Quant(Quant {
                                    ty: QuantType::Exists,
                                    bindings: vec![(name, sort.clone())],
                                }); valid];
                            term![IMPLIES; sat.clone(), some_valid]
                        };
                        vcs.push(
                            Vc::valid(prop, Rt::Var, condition)
                                .sort(&sort)
                                .public(public),
                        )
                    }
                }
            }
        }
        vcs
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

    /// VCs for the correctness of all conversion rules.
    fn conv_vcs(bnd: &Bound) -> Vec<Vc> {
        Self::valid_conversions(bnd)
            .into_iter()
            .flat_map(|(from, to, sort)| {
                [Sound, Complete].iter().map(move |prop| {
                    let mut b = Builder::<Self>::new(bnd);
                    let (enc_in, t_in) = b.valid_enc("a", &sort, from);
                    let (valid_conv, enc_out) = b.capture(|c| enc_in.convert(c, to));
                    let valid_out = enc_out.is_valid(t_in);
                    let condition = if prop.trust() {
                        b.sub(&term![AND; valid_conv.clone(), valid_out.clone()])
                    } else {
                        term![IMPLIES; valid_conv, valid_out]
                    };
                    Vc::valid(*prop, Rt::Conv, condition)
                        .sort(&sort)
                        .from(from)
                        .to(to)
                })
            })
            .collect()
    }

    /// List all configurations valid for this operator rule
    fn op_cfgs(rule: &Rule<Self>, bnd: &Bound) -> Vec<(Sort, Op, Vec<Sort>)> {
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

    /// VCs for the correctness of all operator rules.
    fn op_vcs(rule: &Rule<Self>, bnd: &Bound) -> Vec<Vc> {
        Self::op_cfgs(rule, bnd)
            .into_iter()
            .flat_map(|(sort, op, arg_sorts)| {
                [Sound, Complete].iter().map(move |prop| {
                    let vars = gen_vars(arg_sorts.clone());
                    let mut b = Builder::<Self>::new(&bnd);

                    let e_args: Vec<_> = vars
                        .iter()
                        .enumerate()
                        .map(|(i, (name, sort, _))| b.valid_enc(name, sort, rule.encoding_ty(i)))
                        .collect();

                    let t = term(op.clone(), e_args.iter().map(|tup| tup.1.clone()).collect());
                    let (sat, e_t) = b.capture(|c| {
                        rule.apply(c, &t.op, &e_args.iter().map(|t| &t.0).collect::<Vec<_>>())
                    });
                    let valid_out = e_t.is_valid(t);
                    let condition = if prop.trust() {
                        b.sub(&term![AND; sat, valid_out])
                    } else {
                        term![IMPLIES; sat.clone(), valid_out.clone()]
                    };

                    Vc::valid(*prop, Rt::Op, condition)
                        .sort(&sort)
                        .op(&op)
                        .arg_sorts(&arg_sorts)
                })
            })
            .collect()
    }

    /// Create formulas that are SAT iff some const encoding rule is incorrect.
    fn complete_consts(bnd: &Bound) -> Vec<Vc> {
        Self::sorts(bnd)
            .into_iter()
            .map(|sort| {
                let var = leaf_term(Op::Var("a".into(), sort.clone()));
                let e = Self::const_(&bnd.field, &var);
                Vc::valid(Complete, Rt::Const, e.is_valid(var)).sort(&sort)
            })
            .collect()
    }

    /// List valid conversions
    fn sort_ty_pairs(bnd: &Bound) -> Vec<(Sort, Self::Type)> {
        let mut out = Vec::new();
        for ty in <Self::Type as EncodingType>::all() {
            for sort in sorts(&ty.sort(), bnd) {
                out.push((sort, ty));
            }
        }
        out
    }

    /// VCs for the correctness of all equality assertion rules.
    fn eq_vcs(bnd: &Bound) -> Vec<Vc> {
        Self::sort_ty_pairs(bnd)
            .into_iter()
            .flat_map(|(sort, ty)| {
                [Sound, Complete]
                    .iter()
                    .map(|prop| {
                        let mut b = Builder::<Self>::new(&bnd);
                        let (a_enc, a_term) = b.valid_enc("a", &sort, ty);
                        let (b_enc, b_term) = b.valid_enc("b", &sort, ty);
                        let (sat, ()) = b.capture(|c| a_enc.assert_eq(c, &b_enc));
                        let condition = if prop.trust() {
                            b.sub(&term![IMPLIES; term![EQ; a_term, b_term], sat])
                        } else {
                            term![IMPLIES; sat, term![EQ; a_term, b_term]]
                        };
                        Vc::valid(*prop, Rt::Eq, condition)
                    })
                    .map(|vc| vc.sort(&sort).from(ty))
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    /// VCs that express the uniqueness of terms for valid encodings,
    /// and that to_term and from_term implement the bijection between valid encodings and terms.
    fn uniq_vcs(bnd: &Bound) -> Vec<Vc> {
        Self::sort_ty_pairs(bnd)
            .into_iter()
            .flat_map(|(sort, ty)| {
                let x = Self::floating("x", ty, &bnd.field, &sort);
                let y = Self::floating("y", ty, &bnd.field, &sort);
                let a = leaf_term(Op::Var("a".into(), sort.clone()));
                let b = leaf_term(Op::Var("b".into(), sort.clone()));
                let uniq_enc = term![IMPLIES; term![AND; x.is_valid(a.clone()), y.is_valid(a.clone())], x.eq(&y)];
                let uniq_term = term![IMPLIES; term![AND; x.is_valid(a.clone()), x.is_valid(b.clone())], term![EQ; a.clone(), b.clone()]];
                let from_a = Self::from_term(a.clone(), ty, &bnd.field);
                let from_cor = term![IMPLIES; x.is_valid(a.clone()), from_a.eq(&x)];
                let to_cor = term![IMPLIES; x.is_valid(a.clone()), term![EQ; x.to_term(), a.clone()]];
                vec![
                    Vc::valid(Sound, Rt::UniqEnc, uniq_enc).sort(&sort).from(ty),
                    Vc::valid(Sound, Rt::UniqTerm, uniq_term).sort(&sort).from(ty),
                    Vc::valid(Sound, Rt::FromTerm, from_cor).sort(&sort).from(ty),
                    Vc::valid(Sound, Rt::ToTerm, to_cor).sort(&sort).from(ty),
                ]
            }).collect()
    }

    /// Generate ALL verification conditions
    fn all_vcs(bnd: &Bound) -> Vec<Vc> {
        std::iter::empty()
            .chain(Self::complete_consts(bnd))
            .chain(Self::var_vcs(bnd))
            .chain(Self::conv_vcs(bnd))
            .chain(Self::uniq_vcs(bnd))
            .chain(
                Self::rules()
                    .iter()
                    .flat_map(|rule| Self::op_vcs(rule, bnd)),
            )
            .chain(Self::eq_vcs(bnd))
            .map(Vc::complete)
            .collect()
    }
}

/// The type of property
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Prop {
    /// A satisfiable output implies a satisfiable input.
    Sound,
    /// A satisfiable input implies a satisfiable output.
    Complete,
}

impl Prop {
    /// Should you trust encodings for this type of VC?
    fn trust(&self) -> bool {
        match self {
            Sound => false,
            Complete => true,
        }
    }
}

/// The type of rule
#[derive(Debug, Clone, Copy)]
pub enum RuleType {
    /// variable encoding
    Var,
    /// constant encoding
    Const,
    /// operator lowering
    Op,
    /// conversion
    Conv,
    /// equality assertion
    Eq,
    /// validity uniqueness
    UniqEnc,
    /// validity uniqueness
    UniqTerm,
    /// from term correctness
    FromTerm,
    /// to term correctness
    ToTerm,
}
use RuleType as Rt;

/// A bound for verification
#[derive(Clone)]
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
pub struct Vc {
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
const TAG_PUBLIC: &str = "public";

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
    TAG_PUBLIC,
];

impl Vc {
    fn unsat(prop: Prop, ty: RuleType, formula: Term) -> Self {
        let this = Self {
            tags: Default::default(),
            formula,
        };
        this.tag(TAG_PROP, &format!("{:?}", prop))
            .tag(TAG_TY, &format!("{:?}", ty))
    }
    fn valid(prop: Prop, ty: RuleType, formula: Term) -> Self {
        Vc::unsat(prop, ty, term![NOT; formula])
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
    fn op(self, sort_pat: &Op) -> Self {
        self.tag(TAG_OP_PAT, &format!("{}", OpPat::from(sort_pat)))
    }
    fn from<T: EncodingType>(self, ty: T) -> Self {
        self.tag(TAG_FROM, &format!("{:?}", ty))
    }
    fn to<T: EncodingType>(self, ty: T) -> Self {
        self.tag(TAG_TO, &format!("{:?}", ty))
    }
    fn public(self, public: bool) -> Self {
        self.tag(TAG_PUBLIC, &format!("{}", public))
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

/// Generate variables of sorts
fn gen_vars(sorts: Vec<Sort>) -> Vec<(String, Sort, Term)> {
    fn nth_name(n: usize) -> String {
        assert!(n < 26);
        "abcdefghijklmnopqrst"[n..n + 1].into()
    }
    sorts
        .into_iter()
        .enumerate()
        .map(|(i, s)| (nth_name(i), s.clone(), leaf_term(Op::Var(nth_name(i), s))))
        .collect()
}

fn mk_and(mut ts: Vec<Term>) -> Term {
    match ts.len() {
        0 => bool_lit(true),
        1 => ts.pop().unwrap(),
        _ => term(AND, ts),
    }
}
