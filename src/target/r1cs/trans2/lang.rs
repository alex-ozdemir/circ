//! IR -> Field lowering language

use crate::ir::term::*;
use circ_fields::FieldT;
use fxhash::FxHashMap as HashMap;
use rug::Integer;

#[derive(Debug)]
pub struct RewriteCtx {
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
    pub fn fresh(&mut self, ctx: &str, value: Term) -> Term {
        let i = self.new_variables.len();
        let name = format!("fresh_pf{}_{}", i, ctx);
        self.new_variables.push((value, name.clone()));
        leaf_term(Op::Var(name, Sort::Field(self.field.clone())))
    }
    /// add a new assertion
    pub fn assert(&mut self, t: Term) {
        self.assertions.push(t);
    }
    /// the field
    pub fn field(&self) -> &FieldT {
        &self.field
    }
    /// 0 in the field
    pub fn zero(&self) -> &Term {
        &self.zero
    }
    /// 1 in the field
    pub fn one(&self) -> &Term {
        &self.one
    }
    /// Create a new field constant
    pub fn f_const<I: Into<Integer>>(&self, i: I) -> Term {
        pf_lit(self.field().new_v(i.into()))
    }
}

/// A rewrite rule for lowering IR to a finite-field assertion circuit.
pub struct Rule {
    pattern: Pattern,
    fn_: Box<dyn Fn(&mut RewriteCtx, &Term, &[Term]) -> Term>,
}

impl Rule {
    /// Create a new rule.
    pub fn new<F: Fn(&mut RewriteCtx, &Term, &[Term]) -> Term + 'static>(
        op_pattern: OpPattern,
        sort: Sort,
        f: F,
    ) -> Self {
        Self {
            pattern: Pattern(op_pattern, sort),
            fn_: Box::new(f),
        }
    }

    /// The pattern for this rule
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// Create QF_FF formulas that are SAT iff this rule is unsound.
    pub fn bool_soundness_terms(&self, max_args: usize, field: &FieldT) -> Vec<Term> {
        assert_eq!(self.pattern().1, Sort::Bool);
        let vars_s = self.pattern().generate_inputs(max_args);
        vars_s
            .into_iter()
            .map(|vars| {
                let bool_args: Vec<Term> = vars
                    .iter()
                    .map(|n| leaf_term(Op::Var(n.clone(), Sort::Bool)))
                    .collect();
                let ff_args: Vec<Term> = vars
                    .iter()
                    .map(|n| leaf_term(Op::Var(format!("{}_ff", n), Sort::Field(field.clone()))))
                    .collect();
                let mut ctx = RewriteCtx::new(field.clone());
                for f in &ff_args {
                    ctx.assert(term![EQ; term![PF_MUL; f.clone(), f.clone()], f.clone()]);
                }
                let bool_term = term(self.pattern().get_op(), bool_args.clone());
                let ff_term = (self.fn_)(&mut ctx, &bool_term, &ff_args);
                let mut assertions = Vec::new();
                for (b, f) in bool_args.into_iter().zip(ff_args) {
                    assertions.push(term![EQ; b, term![EQ; f, ctx.one().clone()]]);
                }
                let zero_out = term![EQ; ff_term.clone(), ctx.zero().clone()];
                let one_out = term![EQ; ff_term.clone(), ctx.one().clone()];
                let malencoded_out = term![NOT; term![OR; zero_out, one_out.clone()]];
                let wrong_out = term![NOT; term![EQ; bool_term, one_out]];
                assertions.extend(ctx.assertions);
                assertions.push(term![OR; malencoded_out, wrong_out]);
                term(AND, assertions)
            })
            .collect()
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
/// A pattern for operators
pub enum OpPattern {
    /// Any variable.
    Var,
    /// Any constant.
    Const,
    /// See [Op::Eq].
    Eq,
    /// See [Op::Not].
    Not,
    /// See [Op::Implies].
    Implies,
    /// See [Op::BoolNaryOp].
    BoolNaryOp(BoolNaryOp),
    /// See [Op::PfNaryOp].
    PfNaryOp(PfNaryOp),
    /// See [Op::PfUnOp].
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

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
/// A pattern for sorted operators
pub struct Pattern(pub OpPattern, pub Sort);

impl<'a> From<&'a Term> for Pattern {
    fn from(t: &'a Term) -> Self {
        Pattern(OpPattern::from_op(&t.op), check(&t))
    }
}

impl Pattern {
    fn get_op(&self) -> Op {
        match self.0 {
            OpPattern::Var => Op::Var("DUMMY".into(), self.1.clone()),
            OpPattern::Const => Op::Const(self.1.default_value()),
            OpPattern::Eq => Op::Eq,
            OpPattern::Not => Op::Not,
            OpPattern::Implies => Op::Implies,
            OpPattern::BoolNaryOp(o) => Op::BoolNaryOp(o),
            OpPattern::PfUnOp(o) => Op::PfUnOp(o),
            OpPattern::PfNaryOp(o) => Op::PfNaryOp(o),
        }
    }

    fn generate_inputs(&self, max_args: usize) -> Vec<Vec<String>> {
        fn nth_name(mut n: usize) -> String {
            let mut o = String::new();
            n += 1;
            while n > 0 {
                o.push((b'a' + (n % 26) as u8) as char);
                n /= 26;
            }
            o
        }
        if let Some(n_args) = self.get_op().arity() {
            vec![(0..n_args).map(nth_name).collect()]
        } else {
            (1..max_args)
                .map(|n| (0..n).map(nth_name).collect())
                .collect()
        }
    }
}

/// Apply some rules to translated a computation into a field.
pub fn apply_rules(rs: Vec<Rule>, field: &FieldT, mut computation: Computation) -> Computation {
    assert!(computation.outputs.len() == 1);
    let mut rule_table: HashMap<Pattern, Rule> = HashMap::default();
    for r in rs {
        let prev = rule_table.insert(r.pattern().clone(), r);
        if let Some(p) = prev {
            panic!("Two rules for {:?}", p.pattern())
        }
    }
    let mut rewrite_table: TermMap<Term> = Default::default();
    let mut ctx = RewriteCtx::new(field.clone());
    for t in computation.terms_postorder() {
        let p = Pattern::from(&t);
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
