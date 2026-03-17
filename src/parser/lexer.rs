use crate::interner::Interner;
use crate::parser::error::ParseError;
use crate::parser::token::Token;

pub struct Lexer<'a> {
    source: &'a str,
    bytes: &'a [u8],
    pos: usize,
    line: usize,
    col: usize,
    interner: &'a mut Interner,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str, interner: &'a mut Interner) -> Self {
        Self {
            source,
            bytes: source.as_bytes(),
            pos: 0,
            line: 1,
            col: 1,
            interner,
        }
    }

    pub fn next_token(&mut self) -> Result<Token, ParseError> {
        self.skip_whitespace_and_comments();
        if self.pos >= self.bytes.len() {
            return Ok(Token::Eof);
        }
        todo!("lexer implementation")
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn col(&self) -> usize {
        self.col
    }

    fn skip_whitespace_and_comments(&mut self) {
        todo!()
    }
}
