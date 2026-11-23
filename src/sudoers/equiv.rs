//! Behaviour preservation of the restricted-style parser: the live `parse_lines::<Sudo>` against
//! the legacy parser (`super::legacy`, the code before the rewrite).
//!
//! Both parsers produce values of the same AST types. Each result is printed to text: every
//! field, every span, the message text of every fatal error (the live side renders its error
//! kind). A `Defaults` modifier is a closure; it is printed as its effect on a base `Settings`
//! value (the fields of `Settings::dump_fields` that it changes). [compare] parses the text twice
//! on each side and uses two different bases, so that modifiers which depend on the old value
//! (`+=`, `-=`) are compared on two inputs.
//!
//! Evidence kind: test. Used by the unit tests below (texts of the existing unit tests and a
//! seeded generated corpus) and by the `parser_equiv` fuzz target (`crate::fuzz_api`).

use std::panic::{AssertUnwindSafe, catch_unwind};

use super::ast::*;
use super::basic_parser;
use super::char_stream::{CharStream, chars_of};
use super::legacy;
use super::tokens::*;
use crate::defaults::{self, Settings};

// ------------------------------------------------------------------ printing

fn list<T>(items: &[T], f: impl Fn(&T) -> String) -> String {
    let parts: Vec<String> = items.iter().map(f).collect();
    format!("[{}]", parts.join(", "))
}

fn span(s: &basic_parser::Span) -> String {
    format!("{}:{}-{}:{}", s.start.0, s.start.1, s.end.0, s.end.1)
}

fn identifier(i: &Identifier) -> String {
    match i {
        Identifier::Name(name) => format!("name {:?}", name.as_str()),
        Identifier::ID(id) => format!("id {id}"),
    }
}

fn user_specifier(u: &UserSpecifier) -> String {
    match u {
        UserSpecifier::User(i) => format!("user({})", identifier(i)),
        UserSpecifier::Group(i) => format!("group({})", identifier(i)),
        UserSpecifier::NonunixGroup(i) => format!("nonunix({})", identifier(i)),
    }
}

fn hostname(h: &Hostname) -> String {
    format!("{:?}", h.0)
}

fn pattern(p: &SimpleCommand) -> String {
    format!("{:?}", p.as_str())
}

fn command((p, args): &Command) -> String {
    match args {
        Args::Prefix(a) => format!("{} prefix {:?}", pattern(p), a),
        Args::Exact(a) => format!("{} exact {:?}", pattern(p), a),
    }
}

fn meta<T>(m: &Meta<T>, f: &impl Fn(&T) -> String) -> String {
    match m {
        Meta::All => "ALL".to_string(),
        Meta::Only(x) => format!("only({})", f(x)),
        Meta::Alias(a) => format!("alias {a:?}"),
    }
}

fn spec<T>(s: &Spec<T>, f: &impl Fn(&T) -> String) -> String {
    match s {
        Qualified::Allow(m) => format!("+{}", meta(m, f)),
        Qualified::Forbid(m) => format!("-{}", meta(m, f)),
    }
}

fn spec_list<T>(items: &SpecList<T>, f: impl Fn(&T) -> String) -> String {
    list(items, |s| spec(s, &f))
}

fn chdir(c: &ChDir) -> String {
    match c {
        ChDir::Any => "*".to_string(),
        ChDir::Path(p) => format!("{:?}", &**p),
    }
}

fn modifier(m: &Modifier) -> String {
    match m {
        Modifier::Passwd => "PASSWD".to_string(),
        Modifier::Nopasswd => "NOPASSWD".to_string(),
        Modifier::Setenv => "SETENV".to_string(),
        Modifier::Nosetenv => "NOSETENV".to_string(),
        Modifier::Exec => "EXEC".to_string(),
        Modifier::Noexec => "NOEXEC".to_string(),
        Modifier::Cwd(c) => format!("CWD={}", chdir(c)),
        Modifier::AppArmorProfile(p) => format!("APPARMOR_PROFILE={p:?}"),
        Modifier::Ignored(s) => format!("ignored@{}", span(s)),
        Modifier::NoOp => "noop".to_string(),
    }
}

fn runas(r: &RunAs) -> String {
    format!(
        "({} : {})",
        spec_list(&r.users, user_specifier),
        spec_list(&r.groups, identifier)
    )
}

fn command_spec((r, CommandSpec(tags, cmd)): &(Option<RunAs>, CommandSpec)) -> String {
    format!(
        "{} {} {}",
        r.as_ref().map_or("-".to_string(), runas),
        list(tags, modifier),
        spec(cmd, &command)
    )
}

fn defs<T>(d: &Defs<T>, f: impl Fn(&T) -> String) -> String {
    list(d, |Def(name, items)| format!("{name:?} = {}", spec_list(items, &f)))
}

fn scope(s: &ConfigScope) -> String {
    match s {
        ConfigScope::Generic => "generic".to_string(),
        ConfigScope::Host(h) => format!("host {}", spec_list(h, hostname)),
        ConfigScope::User(u) => format!("user {}", spec_list(u, user_specifier)),
        ConfigScope::RunAs(u) => format!("runas {}", spec_list(u, user_specifier)),
        ConfigScope::Command(c) => format!("command {}", spec_list(c, pattern)),
    }
}

/// The effect of a `Defaults` modifier on `base`: the fields it changes, with their new values.
fn settings_modifier(m: defaults::SettingsModifier, base: &Settings) -> String {
    let before = base.dump_fields();
    let mut settings = base.clone();
    m(&mut settings);
    let changed: Vec<String> = settings
        .dump_fields()
        .into_iter()
        .zip(before)
        .filter(|(after, before)| after != before)
        .map(|((name, value), _)| format!("{name}={value}"))
        .collect();
    format!("{{{}}}", changed.join(" "))
}

fn sudo(item: Sudo, base: &Settings) -> String {
    match item {
        Sudo::Spec(PermissionSpec { users, permissions }) => format!(
            "spec {} {}",
            spec_list(&users, user_specifier),
            list(&permissions, |(hosts, cmds)| format!(
                "{} = {}",
                spec_list(hosts, hostname),
                list(cmds, command_spec)
            ))
        ),
        Sudo::Decl(Directive::UserAlias(d)) => format!("User_Alias {}", defs(&d, user_specifier)),
        Sudo::Decl(Directive::HostAlias(d)) => format!("Host_Alias {}", defs(&d, hostname)),
        Sudo::Decl(Directive::CmndAlias(d)) => format!("Cmnd_Alias {}", defs(&d, command)),
        Sudo::Decl(Directive::RunasAlias(d)) => {
            format!("Runas_Alias {}", defs(&d, user_specifier))
        }
        Sudo::Decl(Directive::Defaults(modifiers, s)) => {
            let effects: Vec<String> = modifiers
                .into_iter()
                .map(|m| settings_modifier(m, base))
                .collect();
            format!("Defaults {} [{}]", scope(&s), effects.join(", "))
        }
        Sudo::Include(path, s) => format!("include {path:?} {}", span(&s)),
        Sudo::IncludeDir(path, s) => format!("includedir {path:?} {}", span(&s)),
        #[cfg(feature = "unstable-remote-sudoers")]
        Sudo::Remote(path, peer, s) => format!(
            "remote {path:?} {} {} {}",
            identifier(&peer.user),
            peer.group.as_ref().map_or("-".to_string(), identifier),
            span(&s)
        ),
        Sudo::LineComment => "comment".to_string(),
    }
}

fn fatal(s: &basic_parser::Span, message: &str) -> String {
    format!("fatal {} {message}", span(s))
}

/// The live parser on `text`, printed; `Err` with the panic message if it panicked.
pub(crate) fn live(text: &str, base: &Settings) -> Result<Vec<String>, String> {
    let run = || {
        let chars = chars_of(&text.to_string());
        basic_parser::parse_lines::<Sudo>(&mut CharStream::from_chars(&chars))
            .into_iter()
            .map(|item| match item {
                Ok(item) => sudo(item, base),
                Err(basic_parser::Status::Fatal(s, kind)) => fatal(&s, &kind.to_string()),
                Err(basic_parser::Status::Reject) => "reject".to_string(),
            })
            .collect()
    };
    catch_unwind(AssertUnwindSafe(run)).map_err(panic_message)
}

/// The legacy parser on `text`, printed; `Err` with the panic message if it panicked.
pub(crate) fn legacy(text: &str, base: &Settings) -> Result<Vec<String>, String> {
    let run = || {
        legacy::parse_lines::<Sudo>(text)
            .into_iter()
            .map(|item| match item {
                Ok(item) => sudo(item, base),
                Err(legacy::Status::Fatal(s, message)) => fatal(&s, &message),
                Err(legacy::Status::Reject) => "reject".to_string(),
            })
            .collect()
    };
    catch_unwind(AssertUnwindSafe(run)).map_err(panic_message)
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        format!("panic: {s}")
    } else if let Some(s) = payload.downcast_ref::<String>() {
        format!("panic: {s}")
    } else {
        "panic".to_string()
    }
}

/// The two bases: the defaults, and a value in which every setting that can be negated is
/// negated and every list holds one extra entry.
pub(crate) fn bases() -> [Settings; 2] {
    let first = Settings::default();
    let mut second = Settings::default();
    for (name, _) in first.dump_fields() {
        if let Some(negate) = defaults::negate(name) {
            negate(&mut second);
        }
        if let Some(defaults::SettingKind::List(checker)) = defaults::set(name) {
            checker(
                defaults::ListMode::Add,
                vec!["SUDO_RS_EQUIV".to_string(), "PATH".to_string()],
            )(&mut second);
        }
    }
    [first, second]
}

/// The printed result of a parser: the items, or the panic message.
pub(crate) type Outcome = Result<Vec<String>, String>;

/// Compare both parsers on `text`. `Ok` holds the common result on the first base; `Err`
/// describes the first difference.
pub(crate) fn compare(text: &str) -> Result<Outcome, String> {
    let mut first = None;
    for base in bases() {
        let old = legacy(text, &base);
        let new = live(text, &base);
        if old != new {
            return Err(format!(
                "input {text:?}\nlegacy: {old:#?}\nlive:   {new:#?}"
            ));
        }
        first.get_or_insert(old);
    }
    Ok(first.unwrap())
}

// ------------------------------------------------------------------ corpus

#[cfg(test)]
mod corpus;

#[cfg(test)]
mod test {
    use super::*;
    use std::io::Write;

    /// Compare on every text; panics with the first differences. Returns the number of texts
    /// and a summary of what the parsers produced on them.
    fn check_all(texts: &[String]) -> (usize, String) {
        let mut failures = Vec::new();
        let mut panics = 0;
        let mut with_fatal = 0;
        let mut items = std::collections::BTreeMap::<&str, usize>::new();
        let mut messages = std::collections::BTreeSet::new();
        for text in texts {
            match compare(text) {
                Err(diff) => failures.push(diff),
                Ok(Err(_)) => panics += 1,
                Ok(Ok(lines)) => {
                    let mut fatal = false;
                    for line in &lines {
                        let kind = line.split(' ').next().unwrap_or("");
                        for known in [
                            "spec", "User_Alias", "Host_Alias", "Cmnd_Alias", "Runas_Alias",
                            "Defaults", "include", "includedir", "comment", "fatal",
                        ] {
                            if kind == known {
                                *items.entry(known).or_default() += 1;
                            }
                        }
                        if kind == "fatal" {
                            fatal = true;
                            // the message without the span
                            let message: String = line.splitn(3, ' ').nth(2).unwrap_or("").into();
                            messages.insert(message);
                        }
                    }
                    with_fatal += usize::from(fatal);
                }
            }
        }
        assert!(
            failures.is_empty(),
            "{} of {} texts differ; the first ones:\n{}",
            failures.len(),
            texts.len(),
            failures[..failures.len().min(5)].join("\n\n")
        );
        let summary = format!(
            "{} texts: {with_fatal} with a fatal error, {panics} panicking (in both parsers); \
             items {items:?}; {} distinct messages",
            texts.len(),
            messages.len()
        );
        (texts.len(), summary)
    }

    #[test]
    fn unit_test_texts() {
        let texts = corpus::unit_test_texts();
        assert!(texts.len() > 500, "only {} texts harvested", texts.len());
        let (n, summary) = check_all(&texts);
        writeln!(
            std::io::stdout(),
            "parser equivalence, unit test texts: no difference on {summary}"
        )
        .unwrap();
        assert!(n > 500);
    }

    #[test]
    fn generated_corpus() {
        let (generated, mutated) = corpus::generated(corpus::SEED, 8_000, 16_000);
        let (n_generated, generated_summary) = check_all(&generated);
        let (n_mutated, mutated_summary) = check_all(&mutated);
        writeln!(
            std::io::stdout(),
            "parser equivalence, generated: no difference on {generated_summary}\n\
             parser equivalence, mutated: no difference on {mutated_summary}"
        )
        .unwrap();
        assert!(n_generated + n_mutated >= 20_000);
    }

    #[test]
    fn bases_differ() {
        let [a, b] = bases();
        assert_ne!(a.dump_fields(), b.dump_fields());
    }

    /// The printer observes what the comparison relies on: items, spans, messages, and the
    /// effect of a `Defaults` modifier on each base.
    #[test]
    fn printer_observes() {
        let text = "Defaults env_keep += \"X\"\nalice ALL = (root) NOPASSWD: /bin/ls, !ALL\nbob ALL = ALL junk\n";
        let [a, b] = bases();
        let on_a = live(text, &a).unwrap();
        let on_b = live(text, &b).unwrap();
        writeln!(std::io::stdout(), "{on_a:#?}\n{on_b:#?}").unwrap();
        assert_eq!(on_a, legacy(text, &a).unwrap());
        assert_ne!(on_a[0], on_b[0]);
    }

    /// `cargo test --lib sudoers::equiv::test::show_samples -- --ignored --nocapture`: a few
    /// generated and mutated texts with the parse result, to inspect the corpus.
    #[test]
    #[ignore]
    fn show_samples() {
        let (generated, mutated) = corpus::generated(corpus::SEED, 8_000, 16_000);
        let texts: Vec<String> = match std::env::var("EQUIV_TEXT") {
            Ok(text) => vec![text],
            Err(_) => generated.into_iter().take(12).chain(mutated.into_iter().take(6)).collect(),
        };
        let [a, _] = bases();
        for text in texts {
            let result = compare(&text).map(|_| ());
            writeln!(std::io::stdout(), "{text:?}\n  {:#?}\n  {result:?}", live(&text, &a)).unwrap();
        }
    }
}
