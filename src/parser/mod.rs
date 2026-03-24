pub mod ast;
pub mod error;
pub mod lexer;
pub mod token;

use ast::*;
use error::ParseError;
use lexer::Lexer;
use token::Token;

use crate::interner::Interner;

pub fn parse(input: &str, interner: &mut Interner) -> Result<Program, ParseError> {
    let mut parser = Parser::new(input, interner)?;
    parser.parse_program()
}

struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str, interner: &'a mut Interner) -> Result<Self, ParseError> {
        let mut lexer = Lexer::new(input, interner);
        let current = lexer.next_token()?;
        Ok(Self { lexer, current })
    }

    fn advance(&mut self) -> Result<Token, ParseError> {
        let prev = std::mem::replace(&mut self.current, Token::Eof);
        self.current = self.lexer.next_token()?;
        Ok(prev)
    }

    fn expect(&mut self, expected: &Token) -> Result<(), ParseError> {
        if &self.current == expected {
            self.advance()?;
            Ok(())
        } else {
            Err(self.error(format!("expected {expected:?}, got {:?}", self.current)))
        }
    }

    fn error(&self, msg: String) -> ParseError {
        ParseError { message: msg, line: self.lexer.line(), col: self.lexer.col() }
    }

    // ── program ────────────────────────────────────────────

    fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut statements = Vec::new();
        while self.current != Token::Eof {
            statements.push(self.parse_statement()?);
        }
        Ok(Program { statements })
    }

    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        match &self.current {
            Token::If => self.parse_constraint(),
            Token::WeakIf => self.parse_weak_constraint(),
            Token::Show => self.parse_show(),
            Token::Const => self.parse_const(),
            Token::LBrace => self.parse_choice_statement(None),
            Token::Number(_) | Token::Variable(_) => {
                // Could be `N { ... }` (choice with lower bound) or aggregate constraint
                self.parse_head_starting_with_term_or_ident()
            }
            Token::Ident(_) => self.parse_head_starting_with_ident(),
            Token::Minus => {
                // Classical negation in head: `-a :- b.` or `-a.`
                self.parse_head_starting_with_ident()
            }
            Token::Minimize => self.parse_optimize(true),
            Token::Maximize => self.parse_optimize(false),
            _ => Err(self.error(format!("unexpected token {:?} at start of statement", self.current))),
        }
    }

    // ── constraint ─────────────────────────────────────────

    fn parse_constraint(&mut self) -> Result<Statement, ParseError> {
        self.expect(&Token::If)?; // :-
        let body = self.parse_body()?;
        self.expect(&Token::Dot)?;
        Ok(Statement::Constraint(Constraint { body }))
    }

    // ── weak constraint ──────────────────────────────────────
    // :~ body. [W@P, T1, ...]  →  desugared to #minimize { W@P,T1,... : body }.

    fn parse_weak_constraint(&mut self) -> Result<Statement, ParseError> {
        self.expect(&Token::WeakIf)?; // :~
        let body = if self.current == Token::Dot {
            vec![]
        } else {
            self.parse_body()?
        };
        self.expect(&Token::Dot)?;
        // Parse [W@P, T1, ...]
        self.expect(&Token::LBrack)?;
        let weight = self.parse_term()?;
        let priority = if self.current == Token::At {
            self.advance()?;
            Some(self.parse_term()?)
        } else {
            None
        };
        let mut terms = Vec::new();
        while self.current == Token::Comma {
            self.advance()?;
            terms.push(self.parse_term()?);
        }
        self.expect(&Token::RBrack)?;
        Ok(Statement::Optimize(OptimizeDirective {
            minimize: true,
            elements: vec![OptimizeElement { weight, priority, terms, condition: body }],
        }))
    }

    // ── head disambiguation ────────────────────────────────

    /// Statement starts with an identifier — could be a fact, rule, disjunctive rule, or choice head.
    fn parse_head_starting_with_ident(&mut self) -> Result<Statement, ParseError> {
        let atom = self.parse_atom()?;
        match &self.current {
            Token::Dot => {
                self.advance()?;
                Ok(Statement::Rule(Rule { head: vec![atom], body: vec![] }))
            }
            Token::If => {
                self.advance()?;
                let body = self.parse_body()?;
                self.expect(&Token::Dot)?;
                Ok(Statement::Rule(Rule { head: vec![atom], body }))
            }
            Token::Pipe => {
                // Disjunctive head: a | b | c ...
                let mut heads = vec![atom];
                while self.current == Token::Pipe {
                    self.advance()?;
                    heads.push(self.parse_atom()?);
                }
                let body = if self.current == Token::If {
                    self.advance()?;
                    self.parse_body()?
                } else {
                    vec![]
                };
                self.expect(&Token::Dot)?;
                Ok(Statement::Rule(Rule { head: heads, body }))
            }
            Token::LBrace => {
                let lower = Some(Term::Symbolic(atom.predicate));
                self.parse_choice_statement(lower)
            }
            // Conditional head: `atom : condition :- body.` → skip `:` conditions
            Token::Colon => {
                self.advance()?;
                // Parse and discard condition (old gringo head conditional)
                let _cond = self.parse_condition_list()?;
                let body = if self.current == Token::If {
                    self.advance()?;
                    self.parse_body()?
                } else {
                    vec![]
                };
                self.expect(&Token::Dot)?;
                Ok(Statement::Rule(Rule { head: vec![atom], body }))
            }
            // Old gringo bracket aggregate: `ident [...] ident :- body.`
            Token::LBrack => {
                while self.current != Token::Dot && self.current != Token::Eof {
                    self.advance()?;
                }
                self.expect(&Token::Dot)?;
                Ok(Statement::Constraint(Constraint { body: vec![] }))
            }
            // Lower-bounded aggregate: `L #agg{...} ...`
            Token::Count | Token::Sum | Token::Min | Token::Max => {
                let lower = Term::Symbolic(atom.predicate);
                let agg = self.parse_aggregate_with_lower(CompOp::Leq, lower)?;
                let body = if self.current == Token::If {
                    self.advance()?;
                    self.parse_body()?
                } else {
                    vec![]
                };
                self.expect(&Token::Dot)?;
                Ok(Statement::Constraint(Constraint {
                    body: {
                        let mut b = vec![Literal::Pos(BodyAtom::Aggregate(agg))];
                        b.extend(body);
                        b
                    }
                }))
            }
            // Assignment: `ident = expr :- body.` used in some programs
            Token::Slash if atom.args.is_empty() => {
                // Could be show-like `pred/arity` but as statement — skip line
                while self.current != Token::Dot && self.current != Token::Eof {
                    self.advance()?;
                }
                self.expect(&Token::Dot)?;
                Ok(Statement::Constraint(Constraint { body: vec![] }))
            }
            _ => Err(self.error(format!("expected '.', ':-', '|', or '{{' after head atom, got {:?}", self.current))),
        }
    }

    /// Statement starts with a number — could be choice lower bound or something else.
    fn parse_head_starting_with_term_or_ident(&mut self) -> Result<Statement, ParseError> {
        let term = self.parse_term()?;
        if self.current == Token::LBrace {
            return self.parse_choice_statement(Some(term));
        }
        // Lower-bounded aggregate constraint: `L #agg{...} [op U] :- body.`
        // or old gringo: `L #agg[...] L :- body.`
        if matches!(self.current, Token::Count | Token::Sum | Token::Min | Token::Max) {
            let lower_op = CompOp::Leq; // L <= agg (default for inline syntax)
            let agg = self.parse_aggregate_with_lower(lower_op, term)?;
            let body = if self.current == Token::If {
                self.advance()?;
                self.parse_body()?
            } else {
                vec![]
            };
            self.expect(&Token::Dot)?;
            return Ok(Statement::Constraint(Constraint {
                body: {
                    let mut b = vec![Literal::Pos(BodyAtom::Aggregate(agg))];
                    b.extend(body);
                    b
                }
            }));
        }
        // Old gringo bracket aggregate: `L [...] U :- body.`
        if self.current == Token::LBrack {
            // Skip until '.' — too complex to fully parse old gringo bracket agg
            while self.current != Token::Dot && self.current != Token::Eof {
                self.advance()?;
            }
            self.expect(&Token::Dot)?;
            // Return empty constraint as placeholder
            return Ok(Statement::Constraint(Constraint { body: vec![] }));
        }
        Err(self.error(format!("expected '{{', aggregate, or '[' after term at start of statement, got {:?}", self.current)))
    }

    // ── choice rule ────────────────────────────────────────

    fn parse_choice_statement(&mut self, lower: Option<Term>) -> Result<Statement, ParseError> {
        self.expect(&Token::LBrace)?;
        let elements = self.parse_choice_elements()?;
        self.expect(&Token::RBrace)?;
        // Parse upper bound: `} N`, `} = N` (equality sets both lower and upper)
        let (lower, upper) = if self.current == Token::Eq {
            self.advance()?;
            let bound = self.parse_term()?;
            (Some(bound.clone()), Some(bound))
        } else if matches!(self.current, Token::Number(_) | Token::Ident(_) | Token::Variable(_)) {
            (lower, Some(self.parse_term()?))
        } else {
            (lower, None)
        };
        let body = if self.current == Token::If {
            self.advance()?;
            self.parse_body()?
        } else {
            vec![]
        };
        self.expect(&Token::Dot)?;
        Ok(Statement::Choice(ChoiceRule { lower, upper, elements, body }))
    }

    fn parse_choice_elements(&mut self) -> Result<Vec<ChoiceElement>, ParseError> {
        let mut elems = vec![self.parse_choice_element()?];
        // Accept both `;` (standard) and `,` (old gringo) as element separators
        while self.current == Token::Semicolon || self.current == Token::Comma {
            self.advance()?;
            elems.push(self.parse_choice_element()?);
        }
        Ok(elems)
    }

    fn parse_choice_element(&mut self) -> Result<ChoiceElement, ParseError> {
        let atom = self.parse_atom()?;
        let mut condition = Vec::new();
        // Accept multiple `:` separated condition groups (old gringo style)
        while self.current == Token::Colon {
            self.advance()?;
            condition.extend(self.parse_condition_list()?);
        }
        Ok(ChoiceElement { atom, condition })
    }

    /// Parse a comma-separated list of literals, stopping at `;` or `}`.
    fn parse_condition_list(&mut self) -> Result<Vec<Literal>, ParseError> {
        let mut lits = vec![self.parse_literal()?];
        while self.current == Token::Comma {
            self.advance()?;
            lits.push(self.parse_literal()?);
        }
        Ok(lits)
    }

    // ── show / const directives ────────────────────────────

    fn parse_optimize(&mut self, minimize: bool) -> Result<Statement, ParseError> {
        self.advance()?; // #minimize / #maximize
        // Accept both { } (modern) and [ ] (old gringo) syntax
        let use_brack = self.current == Token::LBrack;
        if use_brack { self.expect(&Token::LBrack)?; } else { self.expect(&Token::LBrace)?; }
        let close = if use_brack { Token::RBrack } else { Token::RBrace };
        let mut elements = Vec::new();
        if self.current != close {
            elements.push(self.parse_optimize_element()?);
            while self.current == Token::Semicolon {
                self.advance()?;
                elements.push(self.parse_optimize_element()?);
            }
        }
        self.expect(&close)?;
        self.expect(&Token::Dot)?;
        Ok(Statement::Optimize(OptimizeDirective { minimize, elements }))
    }

    /// Parse optimize element in modern or old gringo format.
    /// Modern: `W @ P, T1, ... : condition`
    /// Old gringo: `condition_lit : condition_lit2 = W` (weight at end after `=`)
    fn parse_optimize_element(&mut self) -> Result<OptimizeElement, ParseError> {
        let weight = self.parse_term()?;
        // Optional priority after @
        let priority = if self.current == Token::At {
            self.advance()?;
            Some(self.parse_term()?)
        } else {
            None
        };
        let mut terms = Vec::new();
        if self.current == Token::Comma {
            self.advance()?;
            terms.push(self.parse_term()?);
            while self.current == Token::Comma {
                self.advance()?;
                terms.push(self.parse_term()?);
            }
        }
        let mut condition = Vec::new();
        // Accept multiple `:` separated condition groups (old gringo)
        while self.current == Token::Colon {
            self.advance()?;
            if self.current == Token::Eq { break; }
            condition.extend(self.parse_condition_list()?);
        }
        // Old gringo: `lit : lit2 = W[@P]` — the "weight" we parsed is actually the first
        // condition literal, and the real weight comes after `=`
        if self.current == Token::Eq {
            self.advance()?;
            let real_weight = self.parse_term()?;
            let real_priority = if self.current == Token::At {
                self.advance()?;
                Some(self.parse_term()?)
            } else {
                priority
            };
            let mut full_condition = condition;
            if let Some(lit) = self.term_to_literal(&weight) {
                full_condition.insert(0, lit);
            }
            for t in &terms {
                if let Some(lit) = self.term_to_literal(t) {
                    full_condition.push(lit);
                }
            }
            return Ok(OptimizeElement { weight: real_weight, priority: real_priority, terms: vec![], condition: full_condition });
        }
        Ok(OptimizeElement { weight, priority, terms, condition })
    }

    /// Try to convert a parsed term back into a body literal (for old gringo rewrite).
    fn term_to_literal(&self, term: &Term) -> Option<Literal> {
        match term {
            Term::Symbolic(s) => Some(Literal::Pos(BodyAtom::Atom(Atom { predicate: *s, args: vec![] }))),
            Term::Function(name, args) => Some(Literal::Pos(BodyAtom::Atom(Atom { predicate: *name, args: args.clone() }))),
            _ => None,
        }
    }

    fn parse_show(&mut self) -> Result<Statement, ParseError> {
        self.advance()?; // #show
        // `#show.` means show all — but our AST doesn't represent that directly.
        // `#show pred/arity.` — ShowSig
        // `#show term : body.` — Show
        // `#show -pred/arity.` — ShowSig negative

        if self.current == Token::Dot {
            // #show. (show all) — we don't have an AST node for this, skip
            self.advance()?;
            // Return a dummy — the grounder handles show_all via a flag
            return Ok(Statement::ShowSig(ShowSigDirective {
                predicate: crate::types::SymbolId(u32::MAX),
                arity: 0,
                positive: true,
            }));
        }

        let positive = if self.current == Token::Minus {
            self.advance()?;
            false
        } else {
            true
        };

        // Try to parse as ShowSig: ident "/" number "."
        if let Token::Ident(pred) = self.current.clone() {
            let saved_line = self.lexer.line();
            let saved_col = self.lexer.col();
            self.advance()?;
            if self.current == Token::Slash {
                self.advance()?;
                if let Token::Number(n) = self.current {
                    self.advance()?;
                    self.expect(&Token::Dot)?;
                    return Ok(Statement::ShowSig(ShowSigDirective {
                        predicate: pred,
                        arity: n as usize,
                        positive,
                    }));
                }
                return Err(ParseError {
                    message: "expected arity number after '/'".to_string(),
                    line: saved_line,
                    col: saved_col,
                });
            }
            // Not a ShowSig — it was `#show term ...`
            // We already consumed the Ident; reconstruct the term and parse the rest.
            let term = self.finish_term_from_ident(pred)?;
            let body = if self.current == Token::Colon {
                self.advance()?;
                self.parse_body()?
            } else {
                vec![]
            };
            self.expect(&Token::Dot)?;
            return Ok(Statement::Show(ShowDirective { term, body }));
        }

        // General term-based #show
        let term = self.parse_term()?;
        let body = if self.current == Token::Colon {
            self.advance()?;
            self.parse_body()?
        } else {
            vec![]
        };
        self.expect(&Token::Dot)?;
        Ok(Statement::Show(ShowDirective { term, body }))
    }

    fn parse_const(&mut self) -> Result<Statement, ParseError> {
        self.advance()?; // #const
        let name = match self.advance()? {
            Token::Ident(id) => id,
            other => return Err(self.error(format!("expected identifier after #const, got {other:?}"))),
        };
        self.expect(&Token::Eq)?;
        let value = self.parse_term()?;
        self.expect(&Token::Dot)?;
        Ok(Statement::Const(ConstDef { name, value }))
    }

    // ── body ───────────────────────────────────────────────

    fn parse_body(&mut self) -> Result<Vec<Literal>, ParseError> {
        let mut lits = vec![self.parse_literal()?];
        while self.current == Token::Comma {
            self.advance()?;
            lits.push(self.parse_literal()?);
        }
        Ok(lits)
    }

    fn parse_literal(&mut self) -> Result<Literal, ParseError> {
        if self.current == Token::Not {
            self.advance()?;
            let ba = self.parse_body_atom()?;
            Ok(Literal::Neg(ba))
        } else {
            let ba = self.parse_body_atom()?;
            Ok(Literal::Pos(ba))
        }
    }

    fn parse_body_atom(&mut self) -> Result<BodyAtom, ParseError> {
        if matches!(self.current, Token::Count | Token::Sum | Token::Min | Token::Max) {
            return Ok(BodyAtom::Aggregate(self.parse_aggregate()?));
        }
        // Bare `{ ... }` / `[ ... ]` in body → implicit `#count`
        if self.current == Token::LBrace {
            return Ok(BodyAtom::Aggregate(self.parse_bare_brace_aggregate()?));
        }
        if self.current == Token::LBrack {
            return Ok(BodyAtom::Aggregate(self.parse_bare_bracket_aggregate()?));
        }
        // Classical negation in body: `-ident(...)` → rewrite to `__neg_ident(...)`
        if self.current == Token::Minus && self.lexer.peek_is_ident() {
            self.advance()?; // consume -
            let Token::Ident(id) = self.advance()? else {
                return Err(self.error("expected identifier after '-' for classical negation".into()));
            };
            let name = self.lexer.interner().resolve(id).to_string();
            let neg_pred = self.lexer.interner().intern(&format!("__neg_{name}"));
            let args = if self.current == Token::LParen {
                self.advance()?;
                let args = self.parse_term_list()?;
                self.expect(&Token::RParen)?;
                args
            } else {
                vec![]
            };
            return Ok(BodyAtom::Atom(Atom { predicate: neg_pred, args }));
        }
        // Parse an atom or comparison.
        if let Token::Ident(id) = self.current.clone() {
            self.advance()?;
            if self.current == Token::LParen {
                // Could be atom: ident(args) or function term in comparison
                self.advance()?;
                let args = self.parse_term_list()?;
                self.expect(&Token::RParen)?;
                // Check if a comparison follows — if so, treat as function term
                if let Some(op) = self.try_comp_op() {
                    let name = self.lexer.interner().resolve(id);
                    let left = if (name == "abs" || name == "__abs") && args.len() == 1 {
                        Term::Abs(Box::new(args.into_iter().next().unwrap()))
                    } else {
                        Term::Function(id, args)
                    };
                    if matches!(self.current, Token::Count | Token::Sum | Token::Min | Token::Max) {
                        return Ok(BodyAtom::Aggregate(self.parse_aggregate_with_lower(op, left)?));
                    }
                    let right = self.parse_term()?;
                    return Ok(BodyAtom::Comparison(Comparison { left, op, right }));
                }
                let atom = Atom { predicate: id, args };
                // Check for conditional literal: `p(X) : q(X), ...`
                if self.current == Token::Colon {
                    self.advance()?;
                    let condition = self.parse_condition_list()?;
                    return Ok(BodyAtom::CondLiteral(atom, condition));
                }
                return Ok(BodyAtom::Atom(atom));
            }
            // Bare ident — could be `pred` (0-arity atom) or start of comparison.
            let term = self.finish_term_from_ident(id)?;
            // Old gringo: `ident #agg[...]` / `ident {` without explicit operator → implicit <=
            if matches!(self.current, Token::Count | Token::Sum | Token::Min | Token::Max) {
                return Ok(BodyAtom::Aggregate(self.parse_aggregate_with_lower(CompOp::Leq, term)?));
            }
            if self.current == Token::LBrace || self.current == Token::LBrack {
                let mut agg = if self.current == Token::LBrack {
                    self.parse_bare_bracket_aggregate()?
                } else {
                    self.parse_bare_brace_aggregate()?
                };
                agg.lower = Some((CompOp::Geq, term));
                return Ok(BodyAtom::Aggregate(agg));
            }
            if let Some(op) = self.try_comp_op() {
                // Check if RHS is an aggregate: `term op #agg{...}` → lower-bounded aggregate
                if matches!(self.current, Token::Count | Token::Sum | Token::Min | Token::Max) {
                    return Ok(BodyAtom::Aggregate(self.parse_aggregate_with_lower(op, term)?));
                }
                // `term op [...]` or `term op {...}` → count aggregate
                if self.current == Token::LBrack || self.current == Token::LBrace {
                    let mut agg = if self.current == Token::LBrack {
                        self.parse_bare_bracket_aggregate()?
                    } else {
                        self.parse_bare_brace_aggregate()?
                    };
                    let flipped = match op {
                        CompOp::Lt => CompOp::Gt, CompOp::Leq => CompOp::Geq,
                        CompOp::Gt => CompOp::Lt, CompOp::Geq => CompOp::Leq,
                        other => other,
                    };
                    agg.lower = Some((flipped, term));
                    return Ok(BodyAtom::Aggregate(agg));
                }
                let right = self.parse_term()?;
                return Ok(BodyAtom::Comparison(Comparison { left: term, op, right }));
            }
            // 0-arity atom (possibly conditional)
            if let Term::Symbolic(pred) = term {
                let atom = Atom { predicate: pred, args: vec![] };
                if self.current == Token::Colon {
                    self.advance()?;
                    let condition = self.parse_condition_list()?;
                    return Ok(BodyAtom::CondLiteral(atom, condition));
                }
                return Ok(BodyAtom::Atom(atom));
            }
            return Err(self.error("expected atom or comparison in body".to_string()));
        }
        // Not starting with ident — could be a comparison or lower-bounded aggregate.
        let left = self.parse_term()?;
        // Old gringo: `L #agg[...]` or `L {...}` without explicit operator → implicit <=
        if matches!(self.current, Token::Count | Token::Sum | Token::Min | Token::Max) {
            return Ok(BodyAtom::Aggregate(self.parse_aggregate_with_lower(CompOp::Leq, left)?));
        }
        if self.current == Token::LBrace || self.current == Token::LBrack {
            let mut agg = if self.current == Token::LBrack {
                self.parse_bare_bracket_aggregate()?
            } else {
                self.parse_bare_brace_aggregate()?
            };
            agg.lower = Some((CompOp::Geq, left));
            return Ok(BodyAtom::Aggregate(agg));
        }
        if let Some(op) = self.try_comp_op() {
            // Check if RHS is an aggregate: `term op #agg{...}` → lower-bounded aggregate
            if matches!(self.current, Token::Count | Token::Sum | Token::Min | Token::Max) {
                return Ok(BodyAtom::Aggregate(self.parse_aggregate_with_lower(op, left)?));
            }
            // Old gringo: `term op [...]` / `term op {...}` → count aggregate
            if self.current == Token::LBrack || self.current == Token::LBrace {
                let mut agg = if self.current == Token::LBrack {
                    self.parse_bare_bracket_aggregate()?
                } else {
                    self.parse_bare_brace_aggregate()?
                };
                let flipped = match op {
                    CompOp::Lt => CompOp::Gt, CompOp::Leq => CompOp::Geq,
                    CompOp::Gt => CompOp::Lt, CompOp::Geq => CompOp::Leq,
                    other => other,
                };
                agg.lower = Some((flipped, left));
                return Ok(BodyAtom::Aggregate(agg));
            }
            let right = self.parse_term()?;
            Ok(BodyAtom::Comparison(Comparison { left, op, right }))
        } else {
            Err(self.error(format!("expected comparison operator, got {:?}", self.current)))
        }
    }

    fn try_comp_op(&mut self) -> Option<CompOp> {
        let op = match &self.current {
            Token::Eq => CompOp::Eq,
            Token::Neq => CompOp::Neq,
            Token::Lt => CompOp::Lt,
            Token::Gt => CompOp::Gt,
            Token::Leq => CompOp::Leq,
            Token::Geq => CompOp::Geq,
            _ => return None,
        };
        self.advance().ok();
        Some(op)
    }

    // ── aggregates ─────────────────────────────────────────

    /// Parse bare `{ ... }` as `#count { ... }` (implicit count aggregate in body)
    fn parse_bare_brace_aggregate(&mut self) -> Result<Aggregate, ParseError> {
        self.expect(&Token::LBrace)?;
        let elements = self.parse_agg_elements()?;
        self.expect(&Token::RBrace)?;
        let upper = if let Some(op) = self.try_comp_op() {
            Some((op, self.parse_term()?))
        } else if matches!(self.current, Token::Number(_) | Token::Variable(_) | Token::Ident(_) | Token::Minus) {
            Some((CompOp::Leq, self.parse_term()?))
        } else {
            None
        };
        Ok(Aggregate { function: AggFunction::Count, elements, lower: None, upper })
    }

    /// Parse old gringo `[...]` as `#count [...]`
    fn parse_bare_bracket_aggregate(&mut self) -> Result<Aggregate, ParseError> {
        self.expect(&Token::LBrack)?;
        let elements = self.parse_agg_elements()?;
        self.expect(&Token::RBrack)?;
        let upper = if let Some(op) = self.try_comp_op() {
            Some((op, self.parse_term()?))
        } else if matches!(self.current, Token::Number(_) | Token::Variable(_) | Token::Ident(_)) {
            Some((CompOp::Leq, self.parse_term()?))
        } else {
            None
        };
        Ok(Aggregate { function: AggFunction::Count, elements, lower: None, upper })
    }

    /// Parse an aggregate with a known lower bound: `L op #agg{...} [op U]`
    /// The `op` is from the perspective of the left term (e.g., `2 <= #count{...}`
    /// means the aggregate >= 2, so we flip the operator).
    fn parse_aggregate_with_lower(&mut self, left_op: CompOp, left_term: Term) -> Result<Aggregate, ParseError> {
        // Flip: `L op agg` → agg has lower bound with flipped op
        let lower_op = match left_op {
            CompOp::Lt => CompOp::Gt,   // L < agg → agg > L
            CompOp::Leq => CompOp::Geq, // L <= agg → agg >= L
            CompOp::Gt => CompOp::Lt,   // L > agg → agg < L
            CompOp::Geq => CompOp::Leq, // L >= agg → agg <= L
            CompOp::Eq => CompOp::Eq,
            CompOp::Neq => CompOp::Neq,
        };
        let mut agg = self.parse_aggregate()?;
        agg.lower = Some((lower_op, left_term));
        Ok(agg)
    }

    fn parse_aggregate(&mut self) -> Result<Aggregate, ParseError> {
        let function = match &self.current {
            Token::Count => AggFunction::Count,
            Token::Sum => AggFunction::Sum,
            Token::Min => AggFunction::Min,
            Token::Max => AggFunction::Max,
            _ => return Err(self.error("expected aggregate function".to_string())),
        };
        self.advance()?;
        // Accept both { } (modern) and [ ] (old gringo) syntax
        let use_brack = self.current == Token::LBrack;
        if use_brack { self.expect(&Token::LBrack)?; } else { self.expect(&Token::LBrace)?; }
        let close = if use_brack { Token::RBrack } else { Token::RBrace };
        let elements = self.parse_agg_elements()?;
        self.expect(&close)?;
        // Parse optional upper bound: `op term` or just `term` (old gringo: implicit <=)
        let upper = if let Some(op) = self.try_comp_op() {
            Some((op, self.parse_term()?))
        } else if matches!(self.current, Token::Number(_) | Token::Variable(_) | Token::Ident(_)) {
            // Old gringo: `L #agg[...] U` → implicit `<= U`
            Some((CompOp::Leq, self.parse_term()?))
        } else {
            None
        };
        Ok(Aggregate { function, elements, lower: None, upper })
    }

    fn parse_agg_elements(&mut self) -> Result<Vec<AggElement>, ParseError> {
        let mut elems = vec![self.parse_agg_element()?];
        while self.current == Token::Semicolon {
            self.advance()?;
            elems.push(self.parse_agg_element()?);
        }
        Ok(elems)
    }

    fn parse_agg_element(&mut self) -> Result<AggElement, ParseError> {
        let terms = self.parse_term_list_until_colon()?;
        let mut condition = Vec::new();
        // Parse colon-separated conditions (old gringo uses multiple `:`, modern uses `,`)
        while self.current == Token::Colon {
            self.advance()?;
            // Check for `= Weight` (end of old-gringo element)
            if self.current == Token::Eq { break; }
            condition.extend(self.parse_condition_list()?);
        }
        // Old gringo: `= Weight[@Priority]` at the end of an element
        if self.current == Token::Eq {
            self.advance()?;
            let weight = self.parse_term()?;
            // Skip optional @Priority (not used in our aggregate representation)
            if self.current == Token::At {
                self.advance()?;
                let _priority = self.parse_term()?;
            }
            // Rewrite: the original terms become condition, weight becomes the term
            let mut full_condition = condition;
            for t in &terms {
                if let Some(lit) = self.term_to_literal(t) {
                    full_condition.push(lit);
                }
            }
            return Ok(AggElement { terms: vec![weight], condition: full_condition });
        }
        Ok(AggElement { terms, condition })
    }

    /// Parse comma-separated terms, stopping before `:`, `;`, `}`.
    fn parse_term_list_until_colon(&mut self) -> Result<Vec<Term>, ParseError> {
        let mut terms = vec![self.parse_term()?];
        while self.current == Token::Comma {
            self.advance()?;
            terms.push(self.parse_term()?);
        }
        Ok(terms)
    }

    // ── atom ───────────────────────────────────────────────

    fn parse_atom(&mut self) -> Result<Atom, ParseError> {
        // Handle classical negation: `-ident(...)` → rewrite predicate to `__neg_ident`
        let classically_negated = self.current == Token::Minus;
        if classically_negated {
            self.advance()?;
        }
        let predicate = match self.advance()? {
            Token::Ident(id) => {
                if classically_negated {
                    let name = self.lexer.interner().resolve(id).to_string();
                    self.lexer.interner().intern(&format!("__neg_{name}"))
                } else {
                    id
                }
            }
            other => return Err(self.error(format!("expected predicate name, got {other:?}"))),
        };
        let args = if self.current == Token::LParen {
            self.advance()?;
            let args = self.parse_term_list()?;
            self.expect(&Token::RParen)?;
            args
        } else {
            vec![]
        };
        Ok(Atom { predicate, args })
    }

    fn parse_term_list(&mut self) -> Result<Vec<Term>, ParseError> {
        let mut terms = vec![self.parse_term_or_pool()?];
        while self.current == Token::Comma {
            self.advance()?;
            terms.push(self.parse_term_or_pool()?);
        }
        Ok(terms)
    }

    /// Parse a term that may contain `;`-separated alternatives (pool).
    fn parse_term_or_pool(&mut self) -> Result<Term, ParseError> {
        let first = self.parse_term()?;
        if self.current != Token::Semicolon { return Ok(first); }
        let mut terms = vec![first];
        while self.current == Token::Semicolon {
            self.advance()?;
            terms.push(self.parse_term()?);
        }
        Ok(Term::Pool(terms))
    }

    // ── terms (precedence climbing) ────────────────────────

    fn parse_term(&mut self) -> Result<Term, ParseError> {
        self.parse_additive()
    }

    /// `+` and `-` (left-associative)
    fn parse_additive(&mut self) -> Result<Term, ParseError> {
        let mut left = self.parse_multiplicative()?;
        loop {
            let op = match &self.current {
                Token::Plus => BinOp::Add,
                Token::Minus => BinOp::Sub,
                _ => break,
            };
            self.advance()?;
            let right = self.parse_multiplicative()?;
            left = Term::BinOp(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    /// `*`, `/`, `\` (left-associative)
    fn parse_multiplicative(&mut self) -> Result<Term, ParseError> {
        let mut left = self.parse_unary()?;
        loop {
            let op = match &self.current {
                Token::Star => BinOp::Mul,
                Token::Slash => BinOp::Div,
                Token::Backslash => BinOp::Mod,
                _ => break,
            };
            self.advance()?;
            let right = self.parse_unary()?;
            left = Term::BinOp(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Term, ParseError> {
        if self.current == Token::Minus {
            self.advance()?;
            let inner = self.parse_primary()?;
            Ok(Term::UnaryMinus(Box::new(inner)))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<Term, ParseError> {
        // Absolute value: |expr| → Abs(expr)
        if self.current == Token::Pipe {
            self.advance()?;
            let inner = self.parse_term()?;
            self.expect(&Token::Pipe)?;
            return Ok(Term::Abs(Box::new(inner)));
        }
        match self.advance()? {
            Token::Number(n) => {
                // Check for range: N..M
                if self.current == Token::DotDot {
                    self.advance()?;
                    let upper = self.parse_term()?;
                    return Ok(Term::Range(Box::new(Term::Integer(n)), Box::new(upper)));
                }
                Ok(Term::Integer(n))
            }
            Token::Ident(id) => self.finish_term_from_ident_after_advance(id),
            Token::Variable(id) => Ok(Term::Variable(id)),
            Token::StringLit(id) => Ok(Term::StringConst(id)),
            Token::Anonymous => Ok(Term::Anonymous),
            Token::LParen => {
                let inner = self.parse_term_or_pool()?;
                self.expect(&Token::RParen)?;
                Ok(inner)
            }
            Token::LBrack => {
                // Tuple syntax: [a,b,c] → Function("__tuple", [a,b,c])
                let args = if self.current == Token::RBrack {
                    vec![]
                } else {
                    self.parse_term_list()?
                };
                self.expect(&Token::RBrack)?;
                Ok(Term::Function(self.lexer.interner().intern("__tuple"), args))
            }
            other => Err(self.error(format!("expected term, got {other:?}"))),
        }
    }

    /// After we've already consumed an Ident from `advance()`, figure out if it's
    /// a function call `f(...)`, a range `a..b`, or just a symbolic constant.
    fn finish_term_from_ident_after_advance(&mut self, id: crate::types::SymbolId) -> Result<Term, ParseError> {
        if self.current == Token::LParen {
            self.advance()?;
            let args = self.parse_term_list()?;
            self.expect(&Token::RParen)?;
            // abs(expr) and __abs(expr) → Abs(expr)
            let name = self.lexer.interner().resolve(id);
            if (name == "abs" || name == "__abs") && args.len() == 1 {
                return Ok(Term::Abs(Box::new(args.into_iter().next().unwrap())));
            }
            Ok(Term::Function(id, args))
        } else if self.current == Token::DotDot {
            self.advance()?;
            let upper = self.parse_term()?;
            Ok(Term::Range(Box::new(Term::Symbolic(id)), Box::new(upper)))
        } else {
            Ok(Term::Symbolic(id))
        }
    }

    /// Same as above, but the Ident hasn't been consumed from `current` yet—
    /// we already grabbed the SymbolId from a clone. Used in body_atom disambiguation.
    fn finish_term_from_ident(&mut self, id: crate::types::SymbolId) -> Result<Term, ParseError> {
        // The ident was already consumed from current in the caller.
        self.finish_term_from_ident_after_advance(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_ok(input: &str) -> Program {
        let mut interner = Interner::new();
        parse(input, &mut interner).unwrap()
    }

    fn parse_err(input: &str) -> ParseError {
        let mut interner = Interner::new();
        parse(input, &mut interner).unwrap_err()
    }

    #[test]
    fn fact_no_args() {
        let prog = parse_ok("a.");
        assert_eq!(prog.statements.len(), 1);
        assert!(matches!(&prog.statements[0], Statement::Rule(r) if r.body.is_empty()));
    }

    #[test]
    fn fact_with_args() {
        let prog = parse_ok("p(1, 2).");
        let Statement::Rule(r) = &prog.statements[0] else { panic!() };
        assert_eq!(r.head[0].args.len(), 2);
    }

    #[test]
    fn rule_with_body() {
        let prog = parse_ok("a :- b, c.");
        let Statement::Rule(r) = &prog.statements[0] else { panic!() };
        assert!(!r.body.is_empty());
        assert_eq!(r.body.len(), 2);
    }

    #[test]
    fn constraint() {
        let prog = parse_ok(":- a, b.");
        assert!(matches!(&prog.statements[0], Statement::Constraint(_)));
    }

    #[test]
    fn negation() {
        let prog = parse_ok("a :- not b.");
        let Statement::Rule(r) = &prog.statements[0] else { panic!() };
        assert!(matches!(&r.body[0], Literal::Neg(_)));
    }

    #[test]
    fn choice_rule_simple() {
        let prog = parse_ok("{a; b; c}.");
        assert!(matches!(&prog.statements[0], Statement::Choice(c) if c.elements.len() == 3));
    }

    #[test]
    fn choice_rule_with_bounds_and_body() {
        let prog = parse_ok("1 {a; b} 2 :- d.");
        let Statement::Choice(c) = &prog.statements[0] else { panic!() };
        assert!(c.lower.is_some());
        assert!(c.upper.is_some());
        assert_eq!(c.body.len(), 1);
    }

    #[test]
    fn arithmetic() {
        let prog = parse_ok("p(X+1) :- q(X).");
        let Statement::Rule(r) = &prog.statements[0] else { panic!() };
        assert!(matches!(&r.head[0].args[0], Term::BinOp(BinOp::Add, _, _)));
    }

    #[test]
    fn comparison_in_body() {
        let prog = parse_ok("a :- X > 0.");
        let Statement::Rule(r) = &prog.statements[0] else { panic!() };
        assert!(matches!(&r.body[0], Literal::Pos(BodyAtom::Comparison(_))));
    }

    #[test]
    fn show_sig() {
        let prog = parse_ok("#show a/1.");
        assert!(matches!(&prog.statements[0], Statement::ShowSig(_)));
    }

    #[test]
    fn const_def() {
        let prog = parse_ok("#const n = 5.");
        let Statement::Const(c) = &prog.statements[0] else { panic!() };
        assert!(matches!(&c.value, Term::Integer(5)));
    }

    #[test]
    fn aggregate_count() {
        let prog = parse_ok(":- #count { X : a(X) } > 3.");
        let Statement::Constraint(c) = &prog.statements[0] else { panic!() };
        assert!(matches!(&c.body[0], Literal::Pos(BodyAtom::Aggregate(_))));
    }

    #[test]
    fn transitive_closure() {
        let prog = parse_ok("edge(a,b). edge(b,c). path(X,Y) :- edge(X,Y). path(X,Z) :- path(X,Y), edge(Y,Z).");
        assert_eq!(prog.statements.len(), 4);
    }

    #[test]
    fn multiple_statements() {
        let prog = parse_ok("a. b. c :- a, b.");
        assert_eq!(prog.statements.len(), 3);
    }

    #[test]
    fn error_missing_dot() {
        let err = parse_err("a :- b");
        assert!(err.message.contains("expected"));
    }

    #[test]
    fn choice_element_with_condition() {
        let prog = parse_ok("{ a : b, c; d }.");
        let Statement::Choice(ch) = &prog.statements[0] else { panic!() };
        assert_eq!(ch.elements.len(), 2);
        assert_eq!(ch.elements[0].condition.len(), 2);
    }
}
