//! IR -> Field lowering language

use crate::ir::term::*;
use circ_fields::FieldT;
use rug::Integer;

#[derive(Debug)]
pub(super) struct RewriteCtx {
    pub assertions: Vec<Term>,
    pub new_variables: Vec<(Term, String)>,
    field: FieldT,
    zero: Term,
    one: Term,
}

impl RewriteCtx {
    pub fn new(field: FieldT) -> Self {
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
    // TODO: split zero, one, f_const into extension trait.
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
    pub(super) fn new<F: Fn(&mut RewriteCtx, &Term, &[Term]) -> Term + 'static>(
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

    /// Apply the rule
    pub(super) fn apply(&self, c: &mut RewriteCtx, t: &Term, l_args: &[Term]) -> Term {
        debug_assert_eq!(&Pattern::from(t), &self.pattern);
        (self.fn_)(c, t, l_args)
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
    /// See [Op::BoolMaj].
    BoolMaj,
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
            Op::BoolMaj => OpPattern::BoolMaj,
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

// TODO: split into extension trait.
impl Pattern {
    /// Get all operators that would match this pattern.
    ///
    /// Panics if there isn't a unique operator.
    pub fn get_ops(&self) -> Vec<Op> {
        match self.0 {
            OpPattern::Var => panic!(),
            OpPattern::Const => {
                let iter = self.1.elems_iter_values();
                assert!(iter.size_hint().1.is_some(), "Infinite set");
                iter.map(Op::Const).collect()
            }
            OpPattern::Eq => vec![Op::Eq],
            OpPattern::Not => vec![Op::Not],
            OpPattern::BoolMaj => vec![Op::BoolMaj],
            OpPattern::Implies => vec![Op::Implies],
            OpPattern::BoolNaryOp(o) => vec![Op::BoolNaryOp(o)],
            OpPattern::PfUnOp(o) => vec![Op::PfUnOp(o)],
            OpPattern::PfNaryOp(o) => vec![Op::PfNaryOp(o)],
        }
    }
}
