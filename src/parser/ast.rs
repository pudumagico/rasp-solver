use crate::types::SymbolId;

#[derive(Debug, Clone)]
pub struct Program {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Rule(Rule),
    Constraint(Constraint),
    Choice(ChoiceRule),
    Show(ShowDirective),
    ShowSig(ShowSigDirective),
    Const(ConstDef),
    Optimize(OptimizeDirective),
}

#[derive(Debug, Clone)]
pub struct OptimizeDirective {
    pub minimize: bool,
    pub elements: Vec<OptimizeElement>,
}

#[derive(Debug, Clone)]
pub struct OptimizeElement {
    pub weight: Term,
    pub priority: Option<Term>,
    pub terms: Vec<Term>,
    pub condition: Vec<Literal>,
}

#[derive(Debug, Clone)]
pub struct Rule {
    /// Disjunctive head: `a | b | c :- body.` — single atom for normal rules.
    pub head: Vec<Atom>,
    pub body: Vec<Literal>,
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub body: Vec<Literal>,
}

#[derive(Debug, Clone)]
pub struct ChoiceRule {
    pub lower: Option<Term>,
    pub upper: Option<Term>,
    pub elements: Vec<ChoiceElement>,
    pub body: Vec<Literal>,
}

#[derive(Debug, Clone)]
pub struct ChoiceElement {
    pub atom: Atom,
    pub condition: Vec<Literal>,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Pos(BodyAtom),
    Neg(BodyAtom),
}

#[derive(Debug, Clone)]
pub enum BodyAtom {
    Atom(Atom),
    Comparison(Comparison),
    Aggregate(Aggregate),
}

#[derive(Debug, Clone)]
pub struct Atom {
    pub predicate: SymbolId,
    pub args: Vec<Term>,
}

#[derive(Debug, Clone)]
pub enum Term {
    Variable(SymbolId),
    Integer(i64),
    StringConst(SymbolId),
    Symbolic(SymbolId),
    Function(SymbolId, Vec<Term>),
    BinOp(BinOp, Box<Term>, Box<Term>),
    UnaryMinus(Box<Term>),
    Range(Box<Term>, Box<Term>),
    Anonymous,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, Clone)]
pub struct Comparison {
    pub left: Term,
    pub op: CompOp,
    pub right: Term,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompOp {
    Eq,
    Neq,
    Lt,
    Gt,
    Leq,
    Geq,
}

#[derive(Debug, Clone)]
pub struct Aggregate {
    pub function: AggFunction,
    pub elements: Vec<AggElement>,
    pub lower: Option<(CompOp, Term)>,
    pub upper: Option<(CompOp, Term)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AggFunction {
    Count,
}

#[derive(Debug, Clone)]
pub struct AggElement {
    pub terms: Vec<Term>,
    pub condition: Vec<Literal>,
}

#[derive(Debug, Clone)]
pub struct ShowDirective {
    pub term: Term,
    pub body: Vec<Literal>,
}

#[derive(Debug, Clone)]
pub struct ShowSigDirective {
    pub predicate: SymbolId,
    pub arity: usize,
    pub positive: bool,
}

#[derive(Debug, Clone)]
pub struct ConstDef {
    pub name: SymbolId,
    pub value: Term,
}
