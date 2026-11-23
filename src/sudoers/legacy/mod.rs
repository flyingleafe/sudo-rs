//! The sudoers parser as it was before the restricted-style rewrite (`70fdb56b`, with the
//! `Defaults` block of the current base), kept as the test oracle of the live parser
//! (`crate::sudoers::equiv`). Compiled for tests and fuzzing only.
//!
//! The four files are copies of `src/sudoers/{char_stream,basic_parser,tokens,ast}.rs`, changed
//! only in paths and in what they do not define: the AST and token types, `Span`, `Modifier`
//! and `UserFriendly` are the live ones, so that both parsers build values of the same types.
//! `Directive::could_be_username` became a free function, and the test helpers and unit tests
//! of `basic_parser.rs` were left out.

mod ast;
mod basic_parser;
mod char_stream;
mod tokens;

pub use basic_parser::{Parsed, Status};
pub use char_stream::CharStream;

/// `parse_lines` of the legacy parser, on the whole text.
pub fn parse_lines<T>(text: &str) -> Vec<Parsed<T>>
where
    T: basic_parser::Parse + crate::sudoers::ast_names::UserFriendly,
{
    basic_parser::parse_lines(&mut CharStream::new(text))
}
