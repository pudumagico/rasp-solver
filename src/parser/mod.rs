pub mod ast;
pub mod error;
pub mod lexer;
pub mod token;

use ast::Program;
use error::ParseError;

pub fn parse(_input: &str) -> Result<Program, ParseError> {
    todo!("parser implementation")
}
