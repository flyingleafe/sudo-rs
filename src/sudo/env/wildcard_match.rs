/// The state of [wildcard_match] between two steps.
struct MatchState {
    test_index: usize,
    pattern_index: usize,
    /// A `*` has been seen.
    star: bool,
    /// The test position at which the attempt after the most recent `*` started.
    star_test: usize,
    /// The pattern position after the most recent `*`.
    star_pattern: usize,
    matched: bool,
    /// The match is not decided yet.
    more: bool,
}

/// One step of [wildcard_match]: consume a `*`, a literal, or restart after the most recent
/// `*`; or decide.
fn wildcard_step(test: &[u8], pattern: &[u8], state: MatchState) -> MatchState {
    let mut s = state;
    if s.pattern_index < pattern.len() && s.test_index < test.len() {
        if pattern[s.pattern_index] == b'*' {
            s.pattern_index += 1;
            s.star = true;
            s.star_test = s.test_index;
            s.star_pattern = s.pattern_index;
        } else if pattern[s.pattern_index] == test[s.test_index] {
            s.pattern_index += 1;
            s.test_index += 1;
        } else if s.star {
            s.star_test += 1;
            s.test_index = s.star_test;
            s.pattern_index = s.star_pattern;
        } else {
            s.more = false;
        }
    } else if s.test_index < test.len() {
        if s.star {
            s.star_test += 1;
            s.test_index = s.star_test;
            s.pattern_index = s.star_pattern;
        } else {
            s.more = false;
        }
    } else if s.pattern_index < pattern.len() {
        if pattern[s.pattern_index] == b'*' {
            s.pattern_index += 1;
        } else {
            s.more = false;
        }
    } else {
        s.matched = true;
        s.more = false;
    }
    s
}

/// Match a  test input with a pattern
/// Only wildcard characters (*) in the pattern string have a special meaning: they match on zero or more characters
///
/// Greedy matching that backtracks to the most recent `*` only. The loop repeats
/// [wildcard_step] on one state value until the match is decided (no `return` inside the loop,
/// and a loop state Aeneas can compute a fixed point for), so that Charon/Aeneas extract it;
/// `proofs/lean/SudoRsProofs/EnvFilter.lean` proves it equal to
/// `SudoersSpec.EnvFilter.wildcard`. [wildcard_match_reference] is the implementation before
/// that rewrite; the tests compare both.
pub(super) fn wildcard_match(test: &[u8], pattern: &[u8]) -> bool {
    let mut state = MatchState {
        test_index: 0,
        pattern_index: 0,
        star: false,
        star_test: 0,
        star_pattern: 0,
        matched: false,
        more: true,
    };
    while state.more {
        state = wildcard_step(test, pattern, state);
    }
    state.matched
}

/// The implementation of [wildcard_match] before it was rewritten for extraction; the tests
/// compare both.
#[cfg(test)]
fn wildcard_match_reference(test: &[u8], pattern: &[u8]) -> bool {
    let mut test_index = 0;
    let mut pattern_index = 0;
    let mut last_star = None;

    loop {
        match (pattern.get(pattern_index), test.get(test_index)) {
            (Some(p), Some(t)) => {
                if *p == b'*' {
                    pattern_index += 1;
                    last_star = Some((test_index, pattern_index));
                } else if p == t {
                    pattern_index += 1;
                    test_index += 1;
                } else if let Some((t_index, p_index)) = last_star {
                    test_index = t_index + 1;
                    pattern_index = p_index;
                    last_star = Some((test_index, pattern_index));
                } else {
                    return false;
                }
            }
            (None, Some(_)) => {
                if let Some((t_index, p_index)) = last_star {
                    test_index = t_index + 1;
                    pattern_index = p_index;
                    last_star = Some((test_index, pattern_index));
                } else {
                    return false;
                }
            }
            (Some(b'*'), None) => {
                pattern_index += 1;
            }
            (None, None) => {
                return true;
            }
            _ => {
                return false;
            }
        }
    }
}

/// The definition `SudoersSpec.EnvFilter.wildcard` transcribed: `*` matches any byte string,
/// every other byte itself. Exponential; for tests only.
#[cfg(test)]
fn wildcard_match_definition(test: &[u8], pattern: &[u8]) -> bool {
    match (test, pattern) {
        ([], _) => pattern.iter().all(|c| *c == b'*'),
        (_, []) => false,
        ([_, rest @ ..], [b'*', pattern_rest @ ..]) => {
            wildcard_match_definition(test, pattern_rest) || wildcard_match_definition(rest, pattern)
        }
        ([c, rest @ ..], [d, pattern_rest @ ..]) => {
            c == d && wildcard_match_definition(rest, pattern_rest)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{wildcard_match, wildcard_match_definition, wildcard_match_reference};

    #[test]
    fn test_wildcard_match() {
        let tests = vec![
            ("foo bar", "foo *", true),
            ("foo bar", "foo ba*", true),
            ("foo bar", "foo *ar", true),
            ("foo bar", "foo *r", true),
            ("foo bar", "foo *ab", false),
            ("foo bar", "foo r*", false),
            ("foo bar", "*oo bar", true),
            ("foo bar", "*f* bar", true),
            ("foo bar", "*f bar", false),
            ("foo ", "foo *", true),
            ("foo", "foo *", false),
            ("foo", "foo*", true),
            ("foo bar", "f*******r", true),
            ("foo******bar", "f*r", true),
            ("foo********bar", "foo bar", false),
            ("#%^$V@#TYH%&rot13%#@$%#$%", "#%^$V@#*t13%#@$%#$%", true),
            ("#%^$V@#TYH%&rot13%#@$%#$%", "*%^*%&rot*%#$%", true),
            ("#%^$V@#TYH%&rot13%#@$%#$%", "#%^$V@#TYH%&r*%#@$#$%", false),
            ("#%^$V@#TYH%&rot13%#@$%#$%", "#%^$V@#*******@$%#$%", true),
        ];

        for (test, pattern, expected) in tests.into_iter() {
            assert_eq!(
                wildcard_match(test.as_bytes(), pattern.as_bytes()),
                expected,
                "\"{}\" {} match {}",
                test,
                if expected { "should" } else { "should not" },
                pattern
            );
        }
    }

    /// Every byte string over `alphabet` of length at most `max_len`.
    fn strings(alphabet: &[u8], max_len: usize) -> Vec<Vec<u8>> {
        let mut all = vec![vec![]];
        let mut last = vec![vec![]];
        for _ in 0..max_len {
            let mut next = Vec::new();
            for s in &last {
                for &c in alphabet {
                    let mut t = s.clone();
                    t.push(c);
                    next.push(t);
                }
            }
            all.extend(next.iter().cloned());
            last = next;
        }
        all
    }

    /// Bounded exhaustive comparison: every test string over `{a, b, *}` of length at most 6
    /// against every pattern over `{a, b, *}` of length at most 6 (1093 × 1093 pairs). `*` in the
    /// test string is an ordinary byte.
    #[test]
    fn wildcard_match_equals_reference_and_definition() {
        let all = strings(b"ab*", 6);
        assert_eq!(all.len(), 1093);
        for test in &all {
            for pattern in &all {
                let new = wildcard_match(test, pattern);
                assert_eq!(new, wildcard_match_reference(test, pattern), "{test:?} {pattern:?}");
                assert_eq!(new, wildcard_match_definition(test, pattern), "{test:?} {pattern:?}");
            }
        }
    }

    #[test]
    fn wildcard_match_all_bytes() {
        for c in 0..=u8::MAX {
            for d in 0..=u8::MAX {
                let new = wildcard_match(&[c], &[d]);
                assert_eq!(new, wildcard_match_reference(&[c], &[d]));
                assert_eq!(new, d == b'*' || c == d);
            }
        }
    }
}
