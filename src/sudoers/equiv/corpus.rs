//! Inputs of the equivalence tests: the texts of the existing unit tests, and a deterministic
//! corpus built from a sudoers grammar with a seeded generator and then mutated.

/// Seed of the generated corpus.
pub(super) const SEED: u64 = 0x5eed_0f5e_d0e5_0001;

// ------------------------------------------------------------------ texts of the unit tests

/// Source files whose string literals are harvested (relative to this file).
const SOURCES: &[&str] = &[
    include_str!("../test/mod.rs"),
    include_str!("../test/differential.rs"),
    include_str!("../test/runtime.rs"),
    include_str!("../basic_parser.rs"),
    include_str!("../char_stream.rs"),
    include_str!("../tokens.rs"),
    include_str!("../ast.rs"),
    include_str!("../policy.rs"),
    include_str!("../entry.rs"),
    include_str!("../mod.rs"),
    include_str!("../../defaults/mod.rs"),
    include_str!("../../defaults/settings_dsl.rs"),
];

const EXAMPLE: &str = include_str!("../../../docs/sudoers.example");

/// One token of the literal scanner.
enum Lexeme {
    Literal(String),
    Open,
    Close,
    Other,
}

/// A small lexer for Rust source: string literals (with escapes, raw and byte strings), `[`,
/// `]`; it skips comments and character literals, so that `'"'` does not open a string.
fn lex(src: &str) -> Vec<(usize, Lexeme)> {
    let s: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        if c == '/' && s.get(i + 1) == Some(&'/') {
            while i < s.len() && s[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && s.get(i + 1) == Some(&'*') {
            i += 2;
            while i + 1 < s.len() && !(s[i] == '*' && s[i + 1] == '/') {
                i += 1;
            }
            i += 2;
        } else if c == '\'' {
            // a character literal or a lifetime
            if s.get(i + 1) == Some(&'\\') {
                i += 2;
                while i < s.len() && s[i] != '\'' {
                    i += 1;
                }
                i += 1;
            } else if s.get(i + 2) == Some(&'\'') {
                i += 3;
            } else {
                i += 1;
            }
        } else if c == 'r' && (s.get(i + 1) == Some(&'"') || s.get(i + 1) == Some(&'#'))
            && (i == 0 || !(s[i - 1].is_alphanumeric() || s[i - 1] == '_'))
        {
            let start = i;
            let mut j = i + 1;
            let mut hashes = 0;
            while s.get(j) == Some(&'#') {
                hashes += 1;
                j += 1;
            }
            if s.get(j) != Some(&'"') {
                i += 1;
                continue;
            }
            j += 1;
            let body_start = j;
            loop {
                if j >= s.len() {
                    break;
                }
                if s[j] == '"' && (1..=hashes).all(|k| s.get(j + k) == Some(&'#')) {
                    break;
                }
                j += 1;
            }
            let body: String = s[body_start..j.min(s.len())].iter().collect();
            out.push((start, Lexeme::Literal(body)));
            i = j + 1 + hashes;
        } else if c == '"' {
            let start = i;
            let mut body = String::new();
            i += 1;
            while i < s.len() && s[i] != '"' {
                if s[i] == '\\' && i + 1 < s.len() {
                    let n = s[i + 1];
                    i += 2;
                    match n {
                        'n' => body.push('\n'),
                        't' => body.push('\t'),
                        'r' => body.push('\r'),
                        '0' => body.push('\0'),
                        'x' => {
                            let hex: String = s[i..(i + 2).min(s.len())].iter().collect();
                            body.push(char::from(u8::from_str_radix(&hex, 16).unwrap_or(b'?')));
                            i += 2;
                        }
                        'u' => {
                            let end = (i..s.len()).find(|&k| s[k] == '}').unwrap_or(s.len());
                            let hex: String = s[(i + 1).min(end)..end].iter().collect();
                            body.push(
                                u32::from_str_radix(&hex, 16)
                                    .ok()
                                    .and_then(char::from_u32)
                                    .unwrap_or('?'),
                            );
                            i = end + 1;
                        }
                        '\n' => {
                            while i < s.len() && (s[i] == ' ' || s[i] == '\t') {
                                i += 1;
                            }
                        }
                        other => body.push(other),
                    }
                } else {
                    body.push(s[i]);
                    i += 1;
                }
            }
            i += 1;
            out.push((start, Lexeme::Literal(body)));
        } else if c == '[' {
            out.push((i, Lexeme::Open));
            i += 1;
        } else if c == ']' {
            out.push((i, Lexeme::Close));
            i += 1;
        } else {
            if !c.is_whitespace() {
                out.push((i, Lexeme::Other));
            }
            i += 1;
        }
    }
    out
}

/// Every string literal of the sources (with and without a final newline), the line groups of
/// `sudoer![..]`, `pass!([..])`, `FAIL!([..])` and `SYNTAX!([..])` joined as the macros join
/// them, and `docs/sudoers.example`.
pub(super) fn unit_test_texts() -> Vec<String> {
    let mut texts = std::collections::BTreeSet::new();
    let mut add = |t: String| {
        if !t.ends_with('\n') {
            texts.insert(format!("{t}\n"));
        }
        texts.insert(t);
    };
    for src in SOURCES {
        let chars: Vec<char> = src.chars().collect();
        let lexemes = lex(src);
        for (k, (pos, lexeme)) in lexemes.iter().enumerate() {
            match lexeme {
                Lexeme::Literal(t) => add(t.clone()),
                Lexeme::Open => {
                    // a line group: the literals up to the matching `]`
                    let before: String = chars[pos.saturating_sub(12)..*pos].iter().collect();
                    let before = before.trim_end();
                    if !(before.ends_with("sudoer!")
                        || before.ends_with("pass!(")
                        || before.ends_with("FAIL!(")
                        || before.ends_with("SYNTAX!("))
                    {
                        continue;
                    }
                    let mut depth = 0;
                    let mut group = Vec::new();
                    for (_, l) in &lexemes[k + 1..] {
                        match l {
                            Lexeme::Open => depth += 1,
                            Lexeme::Close if depth == 0 => break,
                            Lexeme::Close => depth -= 1,
                            Lexeme::Literal(t) => group.push(t.clone()),
                            Lexeme::Other => {}
                        }
                    }
                    if !group.is_empty() {
                        add(group.join("\n") + "\n");
                    }
                }
                _ => {}
            }
        }
    }
    add(EXAMPLE.to_string());
    texts.into_iter().collect()
}

// ------------------------------------------------------------------ generator

/// SplitMix64.
pub(super) struct Rng(u64);

impl Rng {
    pub(super) fn new(seed: u64) -> Self {
        Rng(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    /// An entry of `items`; with probability 4/5 one of the first [COMMON] (the well-formed
    /// ones), otherwise any.
    fn pick<'a>(&mut self, items: &[&'a str]) -> &'a str {
        if self.chance(80) {
            items[self.below(items.len().min(COMMON))]
        } else {
            items[self.below(items.len())]
        }
    }
}

/// Every list below starts with this many well-formed entries.
const COMMON: usize = 8;

const USERS: &[&str] = &[
    "alice", "root", "bob", "#1000", "%wheel", "%:nonunix", "ALL", "ADMINS", "#0", "#4294967296",
    "#", "%#20", "%", "%:", "+netgroup", "\"al ice\"", "\"%wheel\"", "\"@x\"", "\"ALL\"",
    "\"a\\\"b\"", "\"\"", "\"alice", "ali\\ ce", "user@host", "user$", "us$er", "Ålice", "ⅧUSER",
    "us\\,er", "!alice", "!!bob", "!!!ADMINS", "! alice", "Defaults", "User_Alias", "_x", "-x",
    ".x", "@x", "ali\\ce", "a\\\nb", "sha224", "ʼn", "ǅx",
];

const HOSTS: &[&str] = &[
    "ALL", "server", "server.example.com", "HOSTS", "SRV_1", "a-b_c", "localhost", "1234",
    "1.2.3.4", "1.2", "123", "1.2.3.4.5", "10.0.0.", ".1", "1..2", "Ⅷ.1.1", "ⅧⅧ.1.1.1", "Ⅷ",
    "HÖST", "٣.1", "!server", "!!HOSTS", "::1", "host:x", "ALL_", "ALLx", "AⅧ", "ÉCOLE", "A B",
];

const RUNAS: &[&str] = &[
    "", "", "", "(root)", "(ALL)", "(ALL:ALL)", "(:wheel)", "(alice, bob)", "(root : wheel, %adm)",
    "()", "(:)", "(!root)", "(ALL", "(root:)", "(RUNAS)", "( root )", "(#0:#0)", "(\"a b\")",
];

const TAGS: &[&str] = &[
    "NOPASSWD:", "PASSWD:", "SETENV:", "NOSETENV:", "EXEC:", "NOEXEC:", "CWD=/tmp", "CWD=*",
    "CWD=~", "CWD=/a*b", "CWD=", "CWD=\"/a b\"", "APPARMOR_PROFILE=foo", "APPARMOR_PROFILE=",
    "LOG_INPUT:", "NOLOG_OUTPUT:", "MAIL:", "FOLLOW:", "NOFOLLOW:", "NOINTERCEPT:", "INTERCEPT:",
    "CHROOT=/", "ROLE=x", "TYPE=y", "TIMEOUT=1", "NOTBEFORE=1", "FOO=bar", "NOPASSWD :",
    "NOPASSWD", "SETENV",
];

const COMMANDS: &[&str] = &[
    "ALL", "/bin/ls", "/usr/bin/su", "/bin/ls -l", "/bin/sh \"\"", "/bin/echo *", "/usr/bin/",
    "sudoedit /etc/hosts", "/bin/echo a*", "/bin/a\\,b", "/bin/a\\ b", "sudoedit", "list",
    "list -x", "sha224:abc /bin/x", "^/bin/x$", "/bin/x ^a", "ls", "CMDS", "!/bin/su",
    "/bin/a\\:b", "/bin/a\\=b", "/bin/x=y", "/bin/\\#x", "/bin/[ab]", "/bin/a\\\\b",
    "/usr/bin/vi /etc/sudoers", "/bin/echo \\\\", "/bin/a\\", "/bin/x\t-y", "/bin/x a\\ b c",
    "/bin/é", "/bin/ls\\\n -l", "/bin/[", "/bin/x **", "\\ ", "/bin/x \\\"\\\"", "s", "l", "/",
];

const DEFAULTS_HEADS: &[&str] = &[
    "Defaults", "Defaults", "Defaults", "Defaults@server", "Defaults:alice", "Defaults!/bin/ls",
    "Defaults>root", "Defaults@server,HOST", "Defaults@1.2.3.4", "Defaults:%wheel,!bob",
    "Defaults!/bin/ls,CMDS", "Defaults >root", "Defaults @x", "Defaults: alice", "Defaultsx",
    "Defaults@", "Defaults!", "Defaults:", "Defaults>",
];

const SETTINGS: &[&str] = &[
    "use_pty", "!use_pty", "env_reset", "env_keep += \"FOO BAR=baz\"", "env_keep -= PATH",
    "secure_path=\"/bin:/usr/bin\"", "passwd_tries=5", "timestamp_timeout=1.5", "!!use_pty",
    "!env_keep", "env_keep = \"A\"", "env_keep=\"\"", "env_check += \"LC_*\"",
    "env_keep += FOO=bar", "secure_path=/bin", "!secure_path", "passwd_tries=1001",
    "passwd_tries=x", "passwd_tries=0x10", "umask=077", "umask=0777", "umask=8",
    "timestamp_timeout=-1", "timestamp_timeout=.", "editor=/usr/bin/vi", "editor=\"/a b\"",
    "runcwd=*", "runcwd=~", "logfile=/x", "!passwd_tries", "use_pty=1", "secure_path",
    "lecture=always", "verifypw=any", "timestamp_type=ppid", "timestamp_type=x",
    "apparmor_profile=unconfined", "env_keep+=\"A\\\"B\"", "env_keep = \"=x\"", "noexec", "rootpw",
    "insults", "!insults", "env_delete -= LD_*", "env_keep=\"A B\" ", "secure_path=\"a\\\\b\"",
    "secure_path=a\\ b", "passwd_timeout=2.25", "env_keep = \"A,B\"", "!", "=", "use_pty !",
    "secure_path=\"\"",
];

const ALIAS_KINDS: &[&str] = &["User_Alias", "Host_Alias", "Cmnd_Alias", "Cmd_Alias", "Runas_Alias"];

const ALIAS_NAMES: &[&str] = &[
    "ADMINS", "HOSTS", "CMDS", "A1", "A_B", "A", "SRV", "X_1", "ALL", "CWD", "ROLE", "CHROOT",
    "lower", "Ⅷ", "_X", "Ab", "ÉA",
];

const OTHER_LINES: &[&str] = &[
    "@include /etc/sudoers.d/x", "@includedir /etc/sudoers.d", "#include /etc/x",
    "#includedir /etc/y", "@include \"/etc/a b\"", "# comment", "", "#1000 ALL=ALL",
    "@include /etc/a\\ b", "@include \"x\\\"y\"", "@include x y", "@include", "@foo", "#include",
    "#1000,alice ALL = ALL", "#1000, alice ALL = ALL", "#x", "#", "@include \"/a\" junk",
    "@includedir \"\"", "@include \"", "@include \"a\\b\"", "#include\t/x", "#includedir",
    "@socket (a) /x", "@include /x\\", "@include\\", " ", "\t", "\\", " \\", "%", ")", "=", "!",
];

/// Characters for mutations and noise: syntax, whitespace, escapes, and Unicode characters with
/// interesting classes (upper case, numeric, white space, control, multi-byte).
const ALPHABET: &[char] = &[
    ' ', '\t', '\n', '\\', '"', '#', ',', ':', '=', '!', '(', ')', '@', '%', '+', '-', '*', '$',
    '/', 'A', 'L', 'a', 'z', '0', '9', '.', '_', '~', '^', '[', 'Ⅷ', 'É', 'ß', '\u{2003}', '\u{a0}',
    '\u{85}', '٣', '\r', '\0', '\u{7f}', '\u{1F600}', '\u{0130}', 'ǅ', '\u{1d400}',
];

fn spaces(rng: &mut Rng) -> &'static str {
    [
        "", "", "", " ", " ", " ", " ", " ", " ", " ", "  ", "  ", "\t", "\t", " \t", "", " ",
        " \\\n", " \\\n  ", "\\\n",
    ][rng.below(20)]
}

fn join_list(rng: &mut Rng, items: &[&str], n: usize) -> String {
    let mut out = String::new();
    for k in 0..n {
        if k > 0 {
            out.push_str(spaces(rng));
            out.push(',');
            out.push_str(spaces(rng));
        }
        out.push_str(rng.pick(items));
    }
    out
}

fn long_token(rng: &mut Rng) -> String {
    let unit = ["a", "é", "Ⅷ", "\u{1F600}", "/", "A"][rng.below(6)];
    let target = [253, 254, 255, 256, 257, 1022, 1023, 1024, 1025, 1026][rng.below(10)];
    let mut s = String::new();
    while s.len() < target {
        s.push_str(unit);
    }
    s
}

fn cmd_spec(rng: &mut Rng) -> String {
    if rng.chance(2) {
        // around the 127-tag limit (`Identifier::LIMIT`)
        let n = [126, 127, 128, 129][rng.below(4)];
        let mut out = String::new();
        for _ in 0..n {
            out.push_str("PASSWD:");
        }
        out.push_str("/bin/ls");
        return out;
    }
    let mut out = rng.pick(RUNAS).to_string();
    out.push_str(spaces(rng));
    for _ in 0..rng.below(3) {
        out.push_str(rng.pick(TAGS));
        out.push_str(spaces(rng));
    }
    if rng.chance(5) {
        out.push('/');
        out.push_str(&long_token(rng));
    } else {
        out.push_str(rng.pick(COMMANDS));
    }
    out
}

fn host_list(rng: &mut Rng) -> String {
    if rng.chance(3) {
        // around the 127-item limit
        let n = [126, 127, 128][rng.below(3)];
        return vec!["h"; n].join(",");
    }
    if rng.chance(3) {
        return long_token(rng);
    }
    let n = 1 + rng.below(3);
    join_list(rng, HOSTS, n)
}

fn rule(rng: &mut Rng) -> String {
    let n = 1 + rng.below(3);
    let mut out = join_list(rng, USERS, n);
    out.push(' ');
    out.push_str(spaces(rng));
    for k in 0..1 + rng.below(2) {
        if k > 0 {
            out.push_str(spaces(rng));
            out.push(':');
            out.push_str(spaces(rng));
        }
        out.push_str(&host_list(rng));
        out.push_str(spaces(rng));
        out.push('=');
        out.push_str(spaces(rng));
        for j in 0..1 + rng.below(3) {
            if j > 0 {
                out.push(',');
                out.push_str(spaces(rng));
            }
            out.push_str(&cmd_spec(rng));
        }
    }
    out
}

fn alias(rng: &mut Rng) -> String {
    let kind = rng.pick(ALIAS_KINDS);
    let mut out = format!("{kind} ");
    for k in 0..1 + rng.below(2) {
        if k > 0 {
            out.push_str(spaces(rng));
            out.push(':');
            out.push_str(spaces(rng));
        }
        out.push_str(rng.pick(ALIAS_NAMES));
        out.push_str(spaces(rng));
        out.push('=');
        out.push_str(spaces(rng));
        let n = 1 + rng.below(3);
        let members = match kind {
            "Host_Alias" => join_list(rng, HOSTS, n),
            "Cmnd_Alias" | "Cmd_Alias" => join_list(rng, COMMANDS, n),
            _ => join_list(rng, USERS, n),
        };
        out.push_str(&members);
    }
    out
}

fn defaults_line(rng: &mut Rng) -> String {
    let mut out = rng.pick(DEFAULTS_HEADS).to_string();
    out.push(' ');
    out.push_str(spaces(rng));
    let n = 1 + rng.below(3);
    out.push_str(&join_list(rng, SETTINGS, n));
    out
}

fn line(rng: &mut Rng) -> String {
    let mut out = String::new();
    if rng.chance(20) {
        out.push_str(spaces(rng));
    }
    let body = match rng.below(10) {
        0..=3 => rule(rng),
        4..=5 => alias(rng),
        6..=7 => defaults_line(rng),
        _ => rng.pick(OTHER_LINES).to_string(),
    };
    out.push_str(&body);
    if rng.chance(10) {
        out.push_str(spaces(rng));
        out.push_str("# trailing comment");
    }
    if rng.chance(10) {
        out.push_str(spaces(rng));
    }
    out
}

/// A text of one to four generated lines.
fn generate(rng: &mut Rng) -> String {
    let mut out = String::new();
    for _ in 0..1 + rng.below(4) {
        out.push_str(&line(rng));
        let terminator = if rng.chance(85) {
            "\n"
        } else {
            ["\r\n", " \\\n", "", "\n\n", " # c\n"][rng.below(5)]
        };
        out.push_str(terminator);
    }
    if rng.chance(10) {
        // drop the final newline
        while out.ends_with('\n') {
            out.pop();
        }
    }
    out
}

/// The mutation operators, applied one to three times to a generated text.
fn mutate(rng: &mut Rng, text: &str, donor: &str) -> String {
    let mut s: Vec<char> = text.chars().collect();
    let d: Vec<char> = donor.chars().collect();
    for _ in 0..1 + rng.below(3) {
        let at = rng.below(s.len() + 1);
        match rng.below(8) {
            // delete a character
            0 if at < s.len() => {
                s.remove(at);
            }
            // insert a character of the alphabet
            1 => s.insert(at, ALPHABET[rng.below(ALPHABET.len())]),
            // replace a character by one of the alphabet
            2 if at < s.len() => s[at] = ALPHABET[rng.below(ALPHABET.len())],
            // duplicate a slice
            3 if at < s.len() => {
                let end = (at + 1 + rng.below(8)).min(s.len());
                let piece: Vec<char> = s[at..end].to_vec();
                s.splice(at..at, piece);
            }
            // swap two adjacent characters
            4 if at + 1 < s.len() => s.swap(at, at + 1),
            // truncate
            5 => s.truncate(at),
            // splice: this prefix, the donor's suffix
            6 => {
                let from = rng.below(d.len() + 1);
                s.truncate(at);
                s.extend_from_slice(&d[from..]);
            }
            // delete a range
            _ if at < s.len() => {
                let end = (at + 1 + rng.below(12)).min(s.len());
                s.drain(at..end);
            }
            _ => s.insert(at, ALPHABET[rng.below(ALPHABET.len())]),
        }
    }
    s.into_iter().collect()
}

/// `n_generated` generated texts and `n_mutated` mutations of them.
pub(super) fn generated(seed: u64, n_generated: usize, n_mutated: usize) -> (Vec<String>, Vec<String>) {
    let mut rng = Rng::new(seed);
    let generated: Vec<String> = (0..n_generated).map(|_| generate(&mut rng)).collect();
    let mutated = (0..n_mutated)
        .map(|_| {
            let base = &generated[rng.below(generated.len())];
            let donor = &generated[rng.below(generated.len())];
            mutate(&mut rng, base, donor)
        })
        .collect();
    (generated, mutated)
}
