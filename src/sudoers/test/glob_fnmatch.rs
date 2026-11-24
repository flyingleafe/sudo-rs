//! Opt-in conformance test of the command-path matcher against libc `fnmatch(3)`; run it with
//! `proofs/differential/glob-fnmatch.sh`, which also records the library versions.
//!
//! sudo-rs side: the real `compile_pattern` and `match_command` (no command-line arguments).
//! Reference: `fnmatch(pattern, path, FNM_PATHNAME)` through the test-only
//! `cutils::fnmatch_pathname`. The test never calls `setlocale`, so `fnmatch` runs in the C
//! locale.
//!
//! Fixture: `/fx/` followed by up to three tokens from `TOKENS` (literals, `/`, `?`, `*`, and
//! closed bracket expressions with a list, `!` negation or an ascending range), against `/fx/`
//! followed by up to three characters from `ALPHABET`. Patterns containing `**` are skipped. The
//! invalid controls must be rejected by `compile_pattern` and are not compared.
//!
//! Not tested: `**`, `^` negation, POSIX classes, backslash escapes, `/` inside brackets,
//! unterminated brackets beyond the controls, `FNM_PERIOD`/`FNM_CASEFOLD`/`FNM_NOESCAPE`,
//! locales other than C, non-ASCII or non-UTF-8 paths, `SimpleCommand::construct` (path
//! canonicalisation, trailing `/`), argument matching, and C sudo itself.

use std::ffi::{CString, OsString};
use std::io::Write;
use std::path::PathBuf;

use super::super::basic_parser::ErrorKind;
use super::super::match_command;
use super::super::tokens::{Args, Command, compile_pattern};
use crate::cutils::fnmatch_pathname;

const PREFIX: &str = "/fx/";
const TOKENS: [&str; 9] = ["a", "b", ".", "/", "?", "*", "[ab]", "[!a]", "[a-c]"];
const ALPHABET: [char; 5] = ['a', 'b', 'c', '.', '/'];
const MAX_LEN: usize = 3;
const INVALID: [&str; 2] = ["/fx/[ab", "/fx/***"];

fn for_each_word<T: Copy>(
    symbols: &[T],
    max_len: usize,
    word: &mut Vec<T>,
    f: &mut impl FnMut(&[T]),
) {
    f(word);
    if word.len() < max_len {
        for &symbol in symbols {
            word.push(symbol);
            for_each_word(symbols, max_len, word, f);
            word.pop();
        }
    }
}

#[test]
#[ignore = "opt-in conformance check: proofs/differential/glob-fnmatch.sh"]
fn glob_fnmatch_conformance() {
    let mut paths = Vec::new();
    for_each_word(&ALPHABET, MAX_LEN, &mut Vec::new(), &mut |chars: &[char]| {
        let text: String = PREFIX.chars().chain(chars.iter().copied()).collect();
        paths.push((CString::new(text.as_str()).unwrap(), PathBuf::from(text)));
    });
    let no_args: &[OsString] = &[];
    let matchers: Vec<_> = paths
        .iter()
        .map(|(_, path)| match_command((path.as_path(), no_args)))
        .collect();

    let (mut patterns, mut matches, mut nonmatches, mut disagreements) = (0u64, 0u64, 0u64, 0u64);
    let mut text = String::new();
    for_each_word(&TOKENS, MAX_LEN, &mut Vec::new(), &mut |tokens: &[&str]| {
        text.clear();
        text.push_str(PREFIX);
        tokens.iter().for_each(|token| text.push_str(token));
        if text.contains("**") {
            return;
        }
        let pattern = match compile_pattern(&text) {
            Ok(pattern) => pattern,
            Err(error) => panic!("fixture pattern rejected: {error:?}"),
        };
        let c_pattern = CString::new(text.as_str()).unwrap();
        let command: Command = (pattern, Args::Prefix(Box::default()));
        patterns += 1;
        for (matcher, (c_path, _)) in matchers.iter().zip(&paths) {
            let glob = matcher(&command);
            match (glob, fnmatch_pathname(&c_pattern, c_path).expect("fnmatch failed")) {
                (true, true) => matches += 1,
                (false, false) => nonmatches += 1,
                _ => disagreements += 1,
            }
        }
    });

    let mut rejected = 0u64;
    for text in INVALID {
        if let Err(ErrorKind::WildcardPattern(_)) = compile_pattern(&text.to_string()) {
            rejected += 1;
        }
    }

    writeln!(
        std::io::stdout(),
        "\nglob-fnmatch-summary patterns={patterns} paths={} pairs={} matches={matches} \
         nonmatches={nonmatches} disagreements={disagreements} invalid_rejected={rejected}/{}",
        paths.len(),
        patterns * paths.len() as u64,
        INVALID.len()
    )
    .unwrap();
    assert!(matches > 0 && nonmatches > 0, "vacuous fixture");
    assert_eq!(rejected, INVALID.len() as u64, "an invalid control was accepted");
    assert_eq!(disagreements, 0, "matchers disagree on the fixture");
}
