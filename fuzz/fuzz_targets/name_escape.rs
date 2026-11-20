//! (h) `NameOrId::parse` (how `sudo -u`/`-g` and `su` read `name` or `#id`) and `escaped`
//! (how `sudo -s`/`sudo -i` turn the command line into the single `-c` argument of the
//! shell), `src/common/{resolve,command}.rs`.
//!
//! Input byte 0 selects the function; the rest is the user name (UTF-8, other inputs are
//! skipped), or the argument list (NUL-separated, any bytes). Asserts:
//! - `NameOrId::parse`: the empty string is rejected; an input without a leading `#` is a name,
//!   unchanged; an input with a leading `#` is never a name, and is an id exactly when the rest
//!   parses as a `uid_t`; an id prints back (`#<id>`) to the same id.
//! - `escaped`: every byte outside `[A-Za-z0-9_$-]` is preceded by a backslash, so arguments
//!   are separated by the only unescaped spaces; splitting there and removing the escapes gives
//!   back the arguments (the escaping is injective on non-empty argument lists);
//!   `CommandAndArguments::build_from_args` with a shell passes `-c` and that string.
#![no_main]

use std::ffi::OsString;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::path::Path;

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::{NameOrId, escaped, name_or_id, shell_arguments};

/// Split at unescaped spaces and remove the escapes.
fn unescape(s: &[u8]) -> Vec<Vec<u8>> {
    let mut args = vec![Vec::new()];
    let mut bytes = s.iter();
    while let Some(&b) = bytes.next() {
        match b {
            b'\\' => {
                let next = *bytes.next().expect("escape at the end of the string");
                args.last_mut().unwrap().push(next);
            }
            b' ' => args.push(Vec::new()),
            _ => {
                assert!(
                    b.is_ascii_alphanumeric() || b"_-$".contains(&b),
                    "unescaped byte {b:#04x}"
                );
                args.last_mut().unwrap().push(b);
            }
        }
    }
    args
}

fuzz_target!(|data: &[u8]| {
    let Some((&mode, rest)) = data.split_first() else {
        return;
    };

    if mode % 2 == 0 {
        let Ok(input) = std::str::from_utf8(rest) else {
            return;
        };
        let parsed = name_or_id(input);
        if input.contains('\0') {
            assert_eq!(parsed, None);
        } else if input.is_empty() {
            assert_eq!(parsed, None, "empty name accepted");
        } else if let Some(digits) = input.strip_prefix('#') {
            assert_eq!(parsed, digits.parse::<u32>().ok().map(NameOrId::Id));
            if let Some(NameOrId::Id(id)) = parsed {
                assert_eq!(name_or_id(&format!("#{id}")), Some(NameOrId::Id(id)));
            }
        } else {
            assert_eq!(parsed, Some(NameOrId::Name(input.to_owned())));
        }
        return;
    }

    let args: Vec<OsString> = rest
        .split(|&b| b == 0)
        .map(|a| OsString::from_vec(a.to_vec()))
        .collect();

    let line = escaped(args.clone());
    let decoded: Vec<OsString> = unescape(line.as_bytes())
        .into_iter()
        .map(OsString::from_vec)
        .collect();
    assert_eq!(decoded, args, "escaping does not decode to the arguments");

    let shell = shell_arguments(Path::new("/nonexistent/sh"), args.clone());
    assert_eq!(shell, vec![OsString::from("-c"), line]);
});
