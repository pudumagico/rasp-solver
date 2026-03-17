use crate::types::SymbolId;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Punctuation
    Dot,
    Comma,
    Semicolon,
    Colon,
    Pipe,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBrack,
    RBrack,

    // Operators
    If,     // :-
    DotDot, // ..
    Not,    // not

    // Arithmetic
    Plus,
    Minus,
    Star,
    Slash,
    Backslash, // mod

    // Comparison
    Eq,  // =  or ==
    Neq, // !=
    Lt,
    Gt,
    Leq,
    Geq,

    // Literals
    Ident(SymbolId),
    Variable(SymbolId),
    Number(i64),
    StringLit(SymbolId),
    Anonymous, // _

    // Directives
    Show,
    Const,
    Count,

    // Special
    Eof,
}
