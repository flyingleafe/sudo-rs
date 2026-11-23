//! A cursor over the characters of a text, with line and column tracking.
//!
//! The parser reads a `&[char]`: the text is converted once, by [chars_of], at the entry points
//! (`read_sudoers`, test helpers). Everything here is written in the restricted style of
//! `proofs/parser/RESTYLE.md`, so that Charon and Aeneas translate it.

#[derive(Clone)]
pub struct CharStream<'a> {
    src: &'a [char],
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> CharStream<'a> {
    pub fn new_with_pos(src: &'a [char], (line, col): (usize, usize)) -> Self {
        CharStream {
            src,
            pos: 0,
            line,
            col,
        }
    }

    pub fn from_chars(src: &'a [char]) -> Self {
        Self::new_with_pos(src, (1, 1))
    }

    /// Moves past `c`, which must be the character at the cursor (`self.peek() == Some(c)`).
    pub fn bump(&mut self, c: char) {
        self.pos += 1;
        if c == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
    }

    pub fn eat_char(&mut self, expect_char: char) -> bool {
        match self.peek() {
            Some(c) if c == expect_char => {
                self.bump(c);
                true
            }
            _ => false,
        }
    }

    pub fn skip_to_newline(&mut self) {
        let mut more = true;
        while more {
            match self.peek() {
                Some(c) if c != '\n' => self.bump(c),
                _ => more = false,
            }
        }
    }

    pub fn peek(&self) -> Option<char> {
        if self.pos < self.src.len() {
            Some(self.src[self.pos])
        } else {
            None
        }
    }

    pub fn get_pos(&self) -> (usize, usize) {
        (self.line, self.col)
    }

    pub fn advance(&mut self, n: usize) {
        let mut i = 0;
        while i < n {
            if let Some(c) = self.peek() {
                self.bump(c);
            }
            i += 1;
        }
    }
}

#[cfg(test)]
impl CharStream<'static> {
    /// Test helper: a stream over a copy of `src` that is never freed.
    pub fn new(src: &str) -> Self {
        let chars: &'static [char] = Vec::leak(src.chars().collect());
        Self::from_chars(chars)
    }
}

/// The characters of a text. Kept opaque for Charon (`Cargo.toml`): `str::chars` and `collect`
/// have no Aeneas model; `proofs/lean/SudoRs/FunsExternal.lean` models it as `String.toList`.
#[allow(clippy::ptr_arg)] // `&String`, not `&str`: the model works on the Lean `String`
pub fn chars_of(text: &String) -> Vec<char> {
    text.chars().collect()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_iter() {
        let mut stream = CharStream::new("12\n3\n");
        assert_eq!(stream.peek(), Some('1'));
        assert!(stream.eat_char('1'));
        assert_eq!(stream.peek(), Some('2'));
        assert!(stream.eat_char('2'));
        assert!(stream.eat_char('\n'));
        assert_eq!(stream.peek(), Some('3'));
        assert!(stream.eat_char('3'));
        assert_eq!(stream.get_pos(), (2, 2));
    }
}
