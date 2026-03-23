use crate::interner::Interner;
use crate::parser::error::ParseError;
use crate::parser::token::Token;

pub struct Lexer<'a> {
    bytes: &'a [u8],
    pos: usize,
    line: usize,
    col: usize,
    interner: &'a mut Interner,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str, interner: &'a mut Interner) -> Self {
        Self { bytes: source.as_bytes(), pos: 0, line: 1, col: 1, interner }
    }

    pub fn next_token(&mut self) -> Result<Token, ParseError> {
        self.skip_whitespace_and_comments();
        if self.pos >= self.bytes.len() {
            return Ok(Token::Eof);
        }
        let start_line = self.line;
        let start_col = self.col;
        let b = self.bytes[self.pos];
        match b {
            b'a'..=b'z' => self.scan_ident_or_keyword(),
            b'A'..=b'Z' => self.scan_variable(),
            b'_' => self.scan_underscore(),
            b'0'..=b'9' => self.scan_number(),
            b'"' => self.scan_string(start_line, start_col),
            b'#' => self.scan_directive(start_line, start_col),
            b':' => {
                self.advance_byte();
                if self.peek() == Some(b'-') {
                    self.advance_byte();
                    Ok(Token::If)
                } else if self.peek() == Some(b'~') {
                    self.advance_byte();
                    Ok(Token::WeakIf)
                } else {
                    Ok(Token::Colon)
                }
            }
            b'.' => {
                self.advance_byte();
                if self.peek() == Some(b'.') {
                    self.advance_byte();
                    Ok(Token::DotDot)
                } else {
                    Ok(Token::Dot)
                }
            }
            b',' => { self.advance_byte(); Ok(Token::Comma) }
            b';' => { self.advance_byte(); Ok(Token::Semicolon) }
            b'|' => { self.advance_byte(); Ok(Token::Pipe) }
            b'(' => { self.advance_byte(); Ok(Token::LParen) }
            b')' => { self.advance_byte(); Ok(Token::RParen) }
            b'{' => { self.advance_byte(); Ok(Token::LBrace) }
            b'}' => { self.advance_byte(); Ok(Token::RBrace) }
            b'[' => { self.advance_byte(); Ok(Token::LBrack) }
            b']' => { self.advance_byte(); Ok(Token::RBrack) }
            b'+' => { self.advance_byte(); Ok(Token::Plus) }
            b'-' => { self.advance_byte(); Ok(Token::Minus) }
            b'*' => { self.advance_byte(); Ok(Token::Star) }
            b'/' => { self.advance_byte(); Ok(Token::Slash) }
            b'\\' => { self.advance_byte(); Ok(Token::Backslash) }
            b'=' => {
                self.advance_byte();
                // both `=` and `==` map to Eq
                if self.peek() == Some(b'=') { self.advance_byte(); }
                Ok(Token::Eq)
            }
            b'!' => {
                self.advance_byte();
                if self.peek() == Some(b'=') {
                    self.advance_byte();
                    Ok(Token::Neq)
                } else {
                    Err(self.error_at(start_line, start_col, "expected '=' after '!'"))
                }
            }
            b'<' => {
                self.advance_byte();
                if self.peek() == Some(b'=') { self.advance_byte(); Ok(Token::Leq) }
                else { Ok(Token::Lt) }
            }
            b'>' => {
                self.advance_byte();
                if self.peek() == Some(b'=') { self.advance_byte(); Ok(Token::Geq) }
                else { Ok(Token::Gt) }
            }
            b'@' => { self.advance_byte(); Ok(Token::At) }
            b'~' => { self.advance_byte(); Ok(Token::Tilde) }
            _ => Err(self.error_at(start_line, start_col, &format!("unexpected character '{}'", b as char))),
        }
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn col(&self) -> usize {
        self.col
    }

    pub fn interner(&mut self) -> &mut Interner {
        self.interner
    }

    /// Check if the next token would be an identifier (lowercase letter at current pos).
    /// Used to disambiguate `-ident` (classical negation) from `-number` (arithmetic).
    pub fn peek_is_ident(&self) -> bool {
        // Skip whitespace to find the actual next character
        let mut i = self.pos;
        while i < self.bytes.len() && self.bytes[i].is_ascii_whitespace() { i += 1; }
        i < self.bytes.len() && self.bytes[i].is_ascii_lowercase()
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn advance_byte(&mut self) -> u8 {
        let b = self.bytes[self.pos];
        self.pos += 1;
        if b == b'\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        b
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // skip whitespace
            while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_whitespace() {
                self.advance_byte();
            }
            if self.pos >= self.bytes.len() { return; }
            if self.bytes[self.pos] == b'%' {
                if self.pos + 1 < self.bytes.len() && self.bytes[self.pos + 1] == b'*' {
                    // block comment: %* ... *%
                    self.advance_byte(); // %
                    self.advance_byte(); // *
                    let mut depth = 1u32;
                    while self.pos < self.bytes.len() && depth > 0 {
                        if self.pos + 1 < self.bytes.len()
                            && self.bytes[self.pos] == b'*'
                            && self.bytes[self.pos + 1] == b'%'
                        {
                            self.advance_byte();
                            self.advance_byte();
                            depth -= 1;
                        } else if self.pos + 1 < self.bytes.len()
                            && self.bytes[self.pos] == b'%'
                            && self.bytes[self.pos + 1] == b'*'
                        {
                            self.advance_byte();
                            self.advance_byte();
                            depth += 1;
                        } else {
                            self.advance_byte();
                        }
                    }
                } else {
                    // line comment: % ... \n
                    while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
                        self.advance_byte();
                    }
                }
                continue; // re-check for more whitespace/comments
            }
            break;
        }
    }

    /// Scan a lowercase-starting identifier or the `not` keyword.
    fn scan_ident_or_keyword(&mut self) -> Result<Token, ParseError> {
        let start = self.pos;
        self.advance_byte();
        // match [a-zA-Z0-9_]*
        while self.pos < self.bytes.len()
            && (self.bytes[self.pos].is_ascii_alphanumeric() || self.bytes[self.pos] == b'_')
        {
            self.advance_byte();
        }
        let word = std::str::from_utf8(&self.bytes[start..self.pos]).unwrap();
        if word == "not" {
            Ok(Token::Not)
        } else {
            Ok(Token::Ident(self.interner.intern(word)))
        }
    }

    /// Scan an uppercase-starting variable.
    fn scan_variable(&mut self) -> Result<Token, ParseError> {
        let start = self.pos;
        self.advance_byte();
        while self.pos < self.bytes.len()
            && (self.bytes[self.pos].is_ascii_alphanumeric() || self.bytes[self.pos] == b'_')
        {
            self.advance_byte();
        }
        let word = std::str::from_utf8(&self.bytes[start..self.pos]).unwrap();
        Ok(Token::Variable(self.interner.intern(word)))
    }

    /// `_` alone → Anonymous, `_Foo123` → Variable.
    fn scan_underscore(&mut self) -> Result<Token, ParseError> {
        let start = self.pos;
        self.advance_byte();
        if self.pos < self.bytes.len()
            && (self.bytes[self.pos].is_ascii_alphanumeric() || self.bytes[self.pos] == b'_')
        {
            while self.pos < self.bytes.len()
                && (self.bytes[self.pos].is_ascii_alphanumeric() || self.bytes[self.pos] == b'_')
            {
                self.advance_byte();
            }
            let word = std::str::from_utf8(&self.bytes[start..self.pos]).unwrap();
            Ok(Token::Variable(self.interner.intern(word)))
        } else {
            Ok(Token::Anonymous)
        }
    }

    fn scan_number(&mut self) -> Result<Token, ParseError> {
        let start = self.pos;
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_digit() {
            self.advance_byte();
        }
        let s = std::str::from_utf8(&self.bytes[start..self.pos]).unwrap();
        let n = s.parse::<i64>().map_err(|_| self.error("integer overflow"))?;
        Ok(Token::Number(n))
    }

    fn scan_string(&mut self, start_line: usize, start_col: usize) -> Result<Token, ParseError> {
        self.advance_byte(); // opening "
        let mut buf = Vec::new();
        loop {
            if self.pos >= self.bytes.len() {
                return Err(self.error_at(start_line, start_col, "unterminated string literal"));
            }
            let b = self.advance_byte();
            if b == b'"' { break; }
            if b == b'\\' {
                if self.pos >= self.bytes.len() {
                    return Err(self.error_at(start_line, start_col, "unterminated string escape"));
                }
                let esc = self.advance_byte();
                match esc {
                    b'"' => buf.push(b'"'),
                    b'\\' => buf.push(b'\\'),
                    b'n' => buf.push(b'\n'),
                    b't' => buf.push(b'\t'),
                    _ => {
                        buf.push(b'\\');
                        buf.push(esc);
                    }
                }
            } else {
                buf.push(b);
            }
        }
        let s = String::from_utf8(buf).map_err(|_| self.error("invalid UTF-8 in string"))?;
        Ok(Token::StringLit(self.interner.intern(&s)))
    }

    /// Scan `#show`, `#const`, `#count` directives.
    fn scan_directive(&mut self, start_line: usize, start_col: usize) -> Result<Token, ParseError> {
        self.advance_byte(); // #
        let start = self.pos;
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_alphabetic() {
            self.advance_byte();
        }
        let word = std::str::from_utf8(&self.bytes[start..self.pos]).unwrap();
        match word {
            "show" => Ok(Token::Show),
            "const" => Ok(Token::Const),
            "count" => Ok(Token::Count),
            "sum" => Ok(Token::Sum),
            "min" => Ok(Token::Min),
            "max" => Ok(Token::Max),
            "minimize" | "minimise" => Ok(Token::Minimize),
            "maximize" | "maximise" => Ok(Token::Maximize),
            _ => Err(self.error_at(start_line, start_col, &format!("unknown directive '#{word}'"))),
        }
    }

    fn error(&self, msg: &str) -> ParseError {
        ParseError { message: msg.to_string(), line: self.line, col: self.col }
    }

    fn error_at(&self, line: usize, col: usize, msg: &str) -> ParseError {
        ParseError { message: msg.to_string(), line, col }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_all(input: &str) -> Vec<Token> {
        let mut interner = Interner::new();
        let mut lexer = Lexer::new(input, &mut interner);
        let mut tokens = Vec::new();
        loop {
            let tok = lexer.next_token().unwrap();
            if tok == Token::Eof { break; }
            tokens.push(tok);
        }
        tokens
    }

    fn lex_err(input: &str) -> ParseError {
        let mut interner = Interner::new();
        let mut lexer = Lexer::new(input, &mut interner);
        loop {
            match lexer.next_token() {
                Err(e) => return e,
                Ok(Token::Eof) => panic!("expected error, got EOF"),
                Ok(_) => {}
            }
        }
    }

    #[test]
    fn empty_input() {
        let mut interner = Interner::new();
        let mut lexer = Lexer::new("", &mut interner);
        assert_eq!(lexer.next_token().unwrap(), Token::Eof);
    }

    #[test]
    fn punctuation_and_operators() {
        let tokens = lex_all(".,;:|(){}[]+-*/\\");
        assert_eq!(tokens, vec![
            Token::Dot, Token::Comma, Token::Semicolon, Token::Colon, Token::Pipe,
            Token::LParen, Token::RParen, Token::LBrace, Token::RBrace,
            Token::LBrack, Token::RBrack,
            Token::Plus, Token::Minus, Token::Star, Token::Slash, Token::Backslash,
        ]);
    }

    #[test]
    fn comparison_operators() {
        let tokens = lex_all("= == != < > <= >=");
        assert_eq!(tokens, vec![
            Token::Eq, Token::Eq, Token::Neq, Token::Lt, Token::Gt, Token::Leq, Token::Geq,
        ]);
    }

    #[test]
    fn multi_char_ops() {
        let tokens = lex_all(":- ..");
        assert_eq!(tokens, vec![Token::If, Token::DotDot]);
    }

    #[test]
    fn identifiers_and_variables() {
        let mut interner = Interner::new();
        let mut lexer = Lexer::new("foo Bar _baz _", &mut interner);
        let t1 = lexer.next_token().unwrap();
        let t2 = lexer.next_token().unwrap();
        let t3 = lexer.next_token().unwrap();
        let t4 = lexer.next_token().unwrap();
        assert!(matches!(t1, Token::Ident(_)));
        assert!(matches!(t2, Token::Variable(_)));
        assert!(matches!(t3, Token::Variable(_))); // _baz is a variable
        assert_eq!(t4, Token::Anonymous);
    }

    #[test]
    fn numbers() {
        let tokens = lex_all("0 42 1000");
        assert_eq!(tokens, vec![Token::Number(0), Token::Number(42), Token::Number(1000)]);
    }

    #[test]
    fn string_literal() {
        let mut interner = Interner::new();
        let mut lexer = Lexer::new(r#""hello""#, &mut interner);
        let tok = lexer.next_token().unwrap();
        if let Token::StringLit(id) = tok {
            assert_eq!(interner.resolve(id), "hello");
        } else {
            panic!("expected StringLit");
        }
    }

    #[test]
    fn keywords_and_directives() {
        let tokens = lex_all("not #show #const #count");
        assert_eq!(tokens, vec![Token::Not, Token::Show, Token::Const, Token::Count]);
    }

    #[test]
    fn line_comment() {
        let tokens = lex_all("a % comment\nb");
        assert_eq!(tokens.len(), 2);
        assert!(matches!(tokens[0], Token::Ident(_)));
        assert!(matches!(tokens[1], Token::Ident(_)));
    }

    #[test]
    fn block_comment() {
        let tokens = lex_all("a %* block\ncomment *% b");
        assert_eq!(tokens.len(), 2);
    }

    #[test]
    fn full_rule() {
        // a(X) :- b(X), not c(X).
        let tokens = lex_all("a(X) :- b(X), not c(X).");
        assert_eq!(tokens.len(), 16);
        assert!(matches!(tokens[0], Token::Ident(_))); // a
        assert_eq!(tokens[1], Token::LParen);
        assert!(matches!(tokens[2], Token::Variable(_))); // X
        assert_eq!(tokens[3], Token::RParen);
        assert_eq!(tokens[4], Token::If);
        assert_eq!(tokens[9], Token::Comma);
        assert_eq!(tokens[10], Token::Not);
        assert_eq!(tokens[15], Token::Dot);
    }

    #[test]
    fn unterminated_string() {
        let err = lex_err(r#""oops"#);
        assert!(err.message.contains("unterminated"));
    }

    #[test]
    fn unknown_directive() {
        let err = lex_err("#bogus");
        assert!(err.message.contains("unknown directive"));
    }

    #[test]
    fn unexpected_char() {
        let err = lex_err("$");
        assert!(err.message.contains("unexpected character"));
    }

    #[test]
    fn at_and_tilde_tokens() {
        let tokens = lex_all("@ ~");
        assert_eq!(tokens, vec![Token::At, Token::Tilde]);
    }

    #[test]
    fn weak_if_token() {
        let tokens = lex_all(":~ :-");
        assert_eq!(tokens, vec![Token::WeakIf, Token::If]);
    }

    #[test]
    fn tracks_line_col() {
        let mut interner = Interner::new();
        let mut lexer = Lexer::new("a\nb", &mut interner);
        lexer.next_token().unwrap(); // a at line 1
        assert_eq!(lexer.line(), 1);
        lexer.next_token().unwrap(); // b at line 2
        assert_eq!(lexer.line(), 2);
        assert_eq!(lexer.col(), 2);
    }
}
