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
            Token::Show => self.parse_show(),
            Token::Const => self.parse_const(),
            Token::LBrace => self.parse_choice_statement(None),
            Token::Number(_) => {
                // Could be `N { ... }` (choice with lower bound) or a fact like `p(1).`
                // We need to try parsing a term and see what follows.
                self.parse_head_starting_with_term_or_ident()
            }
            Token::Ident(_) => self.parse_head_starting_with_ident(),
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
            _ => Err(self.error(format!("expected '.', ':-', '|', or '{{' after head atom, got {:?}", self.current))),
        }
    }

    /// Statement starts with a number — could be choice lower bound or something else.
    fn parse_head_starting_with_term_or_ident(&mut self) -> Result<Statement, ParseError> {
        let term = self.parse_term()?;
        if self.current == Token::LBrace {
            self.parse_choice_statement(Some(term))
        } else {
            Err(self.error(format!("expected '{{' after number at start of statement, got {:?}", self.current)))
        }
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
        while self.current == Token::Semicolon {
            self.advance()?;
            elems.push(self.parse_choice_element()?);
        }
        Ok(elems)
    }

    fn parse_choice_element(&mut self) -> Result<ChoiceElement, ParseError> {
        let atom = self.parse_atom()?;
        let condition = if self.current == Token::Colon {
            self.advance()?;
            self.parse_condition_list()?
        } else {
            vec![]
        };
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
        if self.current == Token::Count {
            return Ok(BodyAtom::Aggregate(self.parse_aggregate()?));
        }
        // Parse an atom or comparison. Comparisons have the form `term op term`.
        // An atom is `ident(...)`. If we see an ident with no parens and it's followed by
        // a comparison operator, it's a comparison (e.g. `X > 0`).
        // Strategy: parse a term, then check if a comparison op follows.
        if let Token::Ident(id) = self.current.clone() {
            self.advance()?;
            if self.current == Token::LParen {
                // Definitely an atom: ident(args)
                self.advance()?;
                let args = self.parse_term_list()?;
                self.expect(&Token::RParen)?;
                let atom = Atom { predicate: id, args };
                // Could still be followed by a comparison op if this is weird,
                // but standard ASP doesn't allow that. Return as atom.
                return Ok(BodyAtom::Atom(atom));
            }
            // Bare ident — could be `pred` (0-arity atom) or start of comparison.
            let term = self.finish_term_from_ident(id)?;
            if let Some(op) = self.try_comp_op() {
                let right = self.parse_term()?;
                return Ok(BodyAtom::Comparison(Comparison { left: term, op, right }));
            }
            // 0-arity atom
            if let Term::Symbolic(pred) = term {
                return Ok(BodyAtom::Atom(Atom { predicate: pred, args: vec![] }));
            }
            // It's some expression that isn't a comparison or atom — error
            return Err(self.error("expected atom or comparison in body".to_string()));
        }
        // Not starting with ident — must be a comparison (e.g. `X > 0`, `1 = 1`).
        let left = self.parse_term()?;
        if let Some(op) = self.try_comp_op() {
            let right = self.parse_term()?;
            Ok(BodyAtom::Comparison(Comparison { left, op, right }))
        } else {
            // Could be a variable used as a 0-arity atom? That's not valid ASP.
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

    fn parse_aggregate(&mut self) -> Result<Aggregate, ParseError> {
        self.advance()?; // #count
        self.expect(&Token::LBrace)?;
        let elements = self.parse_agg_elements()?;
        self.expect(&Token::RBrace)?;
        // Parse optional bounds: `op term` on left (lower) and/or right (upper).
        // Standard form: `L op #count{...} op U` but we handle postfix: `#count{...} op U`.
        // For simplicity, parse right-side bound here.
        let upper = if let Some(op) = self.try_comp_op() {
            Some((op, self.parse_term()?))
        } else {
            None
        };
        Ok(Aggregate { function: AggFunction::Count, elements, lower: None, upper })
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
        let condition = if self.current == Token::Colon {
            self.advance()?;
            self.parse_condition_list()?
        } else {
            vec![]
        };
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
        let predicate = match self.advance()? {
            Token::Ident(id) => id,
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
        let mut terms = vec![self.parse_term()?];
        while self.current == Token::Comma {
            self.advance()?;
            terms.push(self.parse_term()?);
        }
        Ok(terms)
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
                let inner = self.parse_term()?;
                self.expect(&Token::RParen)?;
                Ok(inner)
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
