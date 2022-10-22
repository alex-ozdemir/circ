//! IR -> Field lowering language
#![allow(dead_code)]
#![allow(missing_docs)]

use crate::ir::term::*;
use circ_fields::FieldT;
use fxhash::FxHashMap as HashMap;
use rug::Integer;

struct RewriteCtx {
    assertions: Vec<Term>,
    new_variables: Vec<(Term, String)>,
    field: FieldT,
    zero: Term,
    one: Term,
}

impl RewriteCtx {
    fn new(field: FieldT) -> Self {
        Self {
            assertions: Vec::new(),
            zero: pf_lit(field.new_v(0)),
            one: pf_lit(field.new_v(1)),
            field,
            new_variables: Vec::new(),
        }
    }
    /// Given a value, construct a (fresh) variable meant to be set to this value and return it.
    ///
    /// The context is added to the variable name for debugging.
    fn fresh(&mut self, ctx: &str, value: Term) -> Term {
        let i = self.new_variables.len();
        let name = format!("fresh_pf{}_{}", i, ctx);
        self.new_variables.push((value, name.clone()));
        leaf_term(Op::Var(name, Sort::Field(self.field.clone())))
    }
    fn assert(&mut self, t: Term) {
        self.assertions.push(t);
    }
    fn field(&self) -> &FieldT {
        &self.field
    }
    fn zero(&self) -> &Term {
        &self.zero
    }
    fn one(&self) -> &Term {
        &self.one
    }
    fn f_const<I: Into<Integer>>(&self, i: I) -> Term {
        pf_lit(self.field().new_v(i.into()))
    }
}

struct Rule {
    match_op: OpPattern,
    match_sort: Sort,
    fn_: Box<dyn Fn(&mut RewriteCtx, &Term, &[Term]) -> Term>,
}

impl Rule {
    fn new<F: Fn(&mut RewriteCtx, &Term, &[Term]) -> Term + 'static>(
        match_op: OpPattern,
        match_sort: Sort,
        f: F,
    ) -> Self {
        Self {
            match_op,
            match_sort,
            fn_: Box::new(f),
        }
    }
    fn pattern(&self) -> (OpPattern, Sort) {
        (self.match_op, self.match_sort.clone())
    }
}

fn bool_neg(t: Term) -> Term {
    if let Sort::Field(f) = check(&t) {
        term![PF_ADD; pf_lit(f.new_v(1)), term![PF_NEG; t]]
    } else {
        panic!()
    }
}

fn bool_to_field(t: Term, f: &FieldT) -> Term {
    term![ITE; t, pf_lit(f.new_v(1)), pf_lit(f.new_v(0))]
}

fn rw_is_zero(ctx: &mut RewriteCtx, x: Term) -> Term {
    let eqz = term![Op::Eq; x.clone(), ctx.zero().clone()];
    // m * x - 1 + is_zero == 0
    // is_zero * x == 0
    let m = ctx.fresh(
        "is_zero_inv",
        term![Op::Ite; eqz.clone(), ctx.zero().clone(), term![PF_RECIP; x.clone()]],
    );
    let is_zero = ctx.fresh(
        "is_zero",
        bool_to_field(eqz, ctx.field()),
    );
    ctx.assert(term![EQ; term![PF_MUL; m.clone(), x.clone()], bool_neg(is_zero.clone())]);
    ctx.assert(term![EQ; term![PF_MUL; is_zero.clone(), x], ctx.zero.clone()]);
    is_zero
}

fn rw_ensure_bit(ctx: &mut RewriteCtx, b: Term) {
    let b_minus_one = term![PF_ADD; b.clone(), term![PF_NEG; ctx.one().clone()]];
    ctx.assert(term![EQ; term![PF_MUL; b_minus_one, b], ctx.zero().clone()]);
}
fn rw_bit_split(ctx: &mut RewriteCtx, reason: &str, x: Term, n: usize) -> Vec<Term> {
    let x_bv = term![Op::PfToBv(n); x.clone()];
    let bits: Vec<Term> = (0..n)
        .map(|i| {
            ctx.fresh(
                // We get the right repr here because of infinite two's complement.
                &format!("{}_bit{}", reason, i),
                bool_to_field(term![Op::BvBit(i); x_bv.clone()], ctx.field()),
            )
        })
        .collect();
    let summands: Vec<Term> = bits
        .iter()
        .enumerate()
        .map(|(i, b)| {
            rw_ensure_bit(ctx, b.clone());
            term![PF_MUL; pf_lit(ctx.field().new_v(Integer::from(1) << i)), b.clone()]
        })
        .collect();
    ctx.assert(term![EQ; term(PF_ADD, summands), x]);
    bits
}

fn rw_or_helper(ctx: &mut RewriteCtx, mut l_args: Vec<Term>) -> Term {
    loop {
        match l_args.len() {
            0 => return pf_lit(ctx.field().new_v(0)),
            1 => return l_args[0].clone(),
            2 => {
                return bool_neg(
                    term![PF_MUL; bool_neg(l_args[0].clone()), bool_neg(l_args[1].clone())],
                )
            }
            i => {
                // assumes field is prime
                let take = if ctx.field().modulus() < &i {
                    ctx.field().modulus().to_usize().unwrap()
                } else {
                    i
                };
                let partial_or = bool_neg(rw_is_zero(
                    ctx,
                    term(PF_ADD, l_args.drain(i - take..).collect()),
                ));
                l_args.push(partial_or);
            }
        }
    }
}

fn rw_or(ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    rw_or_helper(ctx, l_args.to_owned())
}

fn rw_and(ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    bool_neg(rw_or_helper(
        ctx,
        l_args.iter().map(|a| bool_neg(a.clone())).collect(),
    ))
}

fn rw_bool_eq(ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    term![PF_ADD;
        ctx.one().clone(),
        term![PF_NEG; l_args[0].clone()],
        term![PF_NEG; l_args[1].clone()],
        term![PF_MUL; l_args[0].clone(), l_args[1].clone()]]
}

fn rw_xor(ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    let mut l_args = l_args.to_owned();
    loop {
        match l_args.len() {
            0 => return pf_lit(ctx.field().new_v(0)),
            1 => return l_args[0].clone(),
            2 => {
                return term![PF_ADD;
                    l_args[0].clone(),
                    l_args[1].clone(),
                    term![PF_NEG; term![PF_MUL; pf_lit(ctx.field().new_v(2)), l_args[0].clone(), l_args[1].clone()]]]
            }
            i => {
                // assumes field is prime
                let take = if ctx.field().modulus() < &i {
                    ctx.field().modulus().to_usize().unwrap()
                } else {
                    i
                };
                let partial_sum = term(PF_ADD, l_args.drain(i - take..).collect());
                let max_sum = partial_sum.cs.len();
                let num_bits = ((max_sum as f64) + 0.2f64).log2() as usize + 1;
                let bits = rw_bit_split(ctx, "xor", partial_sum, num_bits);
                l_args.push(bits[0].clone());
            }
        }
    }
}

fn rw_not(_ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    bool_neg(l_args[0].clone())
}

fn rw_implies(_ctx: &mut RewriteCtx, _term: &Term, l_args: &[Term]) -> Term {
    bool_neg(term![PF_MUL; l_args[0].clone(), bool_neg(l_args[1].clone())])
}

fn rw_var(ctx: &mut RewriteCtx, term: &Term, _l_args: &[Term]) -> Term {
    if let Op::Var(name, sort) = &term.op {
        assert_eq!(sort, &Sort::Bool);
        let f_var = ctx.fresh(&name, bool_to_field(term.clone(), &ctx.field));
        rw_ensure_bit(ctx, f_var.clone());
        f_var
    } else {
        unreachable!()
    }
}

fn rw_const(ctx: &mut RewriteCtx, term: &Term, _l_args: &[Term]) -> Term {
    if let Op::Const(Value::Bool(b)) = &term.op {
        if *b {
            ctx.one().clone()
        } else {
            ctx.zero().clone()
        }
    } else {
        unreachable!()
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
enum OpPattern {
    Var,
    Const,
    Eq,
    Not,
    Implies,
    BoolNaryOp(BoolNaryOp),
    PfNaryOp(PfNaryOp),
    PfUnOp(PfUnOp),
}

impl OpPattern {
    fn from_op(op: &Op) -> Self {
        match op {
            Op::Var(..) => OpPattern::Var,
            Op::Const(..) => OpPattern::Const,
            Op::Eq => OpPattern::Eq,
            Op::Not => OpPattern::Not,
            Op::Implies => OpPattern::Implies,
            Op::BoolNaryOp(b) => OpPattern::BoolNaryOp(*b),
            Op::PfNaryOp(b) => OpPattern::PfNaryOp(*b),
            Op::PfUnOp(b) => OpPattern::PfUnOp(*b),
            _ => unimplemented!("op {}", op),
        }
    }
}

fn rules() -> Vec<Rule> {
    use OpPattern as OpP;
    use Sort::Bool;
    vec![
        Rule::new(OpP::Const, Bool, Box::new(rw_const)),
        Rule::new(OpP::Var, Bool, Box::new(rw_var)),
        Rule::new(OpP::Eq, Bool, Box::new(rw_bool_eq)),
        Rule::new(OpP::Not, Bool, Box::new(rw_not)),
        Rule::new(OpP::Implies, Bool, Box::new(rw_implies)),
        Rule::new(OpP::BoolNaryOp(BoolNaryOp::Xor), Bool, Box::new(rw_xor)),
        Rule::new(OpP::BoolNaryOp(BoolNaryOp::Or), Bool, Box::new(rw_or)),
        Rule::new(OpP::BoolNaryOp(BoolNaryOp::And), Bool, Box::new(rw_and)),
    ]
}

type Pattern = (OpPattern, Sort);

fn term_pattern(t: &Term) -> Pattern {
    (OpPattern::from_op(&t.op), check(&t))
}

fn apply_rules(rs: Vec<Rule>, field: &FieldT, mut computation: Computation) -> Computation {
    assert!(computation.outputs.len() == 1);
    let mut rule_table: HashMap<Pattern, Rule> = HashMap::default();
    for r in rs {
        let prev = rule_table.insert(r.pattern(), r);
        if let Some(p) = prev {
            panic!("Two rules for {:?}", p.pattern())
        }
    }
    let mut rewrite_table: TermMap<Term> = Default::default();
    let mut ctx = RewriteCtx::new(field.clone());
    for t in computation.terms_postorder() {
        let p = term_pattern(&t);
        let r = rule_table
            .get(&p)
            .unwrap_or_else(|| panic!("No pattern for pattern {:?}", p));
        let args: Vec<Term> =
            t.cs.iter()
                .map(|c| rewrite_table.get(c).unwrap().clone())
                .collect();
        let new = (r.fn_)(&mut ctx, &t, &args);
        rewrite_table.insert(t, new);
    }
    let o = rewrite_table.get(&computation.outputs[0]).unwrap().clone();
    ctx.assert(term![EQ; o, ctx.one().clone()]);
    computation.outputs = vec![term(AND, ctx.assertions)];
    for (value, name) in ctx.new_variables {
        computation.extend_precomputation(name, value);
    }
    computation
}

fn apply(field: &FieldT, computation: Computation) -> Computation {
    apply_rules(rules(), field, computation)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::proof::Constraints;
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

    #[test]
    fn or3false() {
        let _ = env_logger::builder().is_test(true).try_init();
        let cs = text::parse_computation(
            b"
            (computation
                (metadata () () ())
                (not (or false false false))
            )
        ",
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
    fn impl_tf() {
        let _ = env_logger::builder().is_test(true).try_init();
        let cs = text::parse_computation(
            b"
            (computation
                (metadata () () ())
                (not (=> true false))
            )
        ",
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
}
