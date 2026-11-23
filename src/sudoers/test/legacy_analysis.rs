//! `analyze`, `Sudoers::specify_host_user_runas` and `Sudoers::specify_command` as they were
//! before the restricted-style rewrite (`d84ff98a`), kept as the test oracle of the live code
//! (`super::analysis`). Compiled for tests only.
//!
//! Copied verbatim, changed only in paths: the two `specify_*` methods are free functions of
//! `this: &mut Sudoers`, and `open_sudoers` / `open_remote_sudoers`, which now return the text,
//! are wrapped below to return the parsed items as they did.

use std::ffi::OsString;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};

use super::super::*;

fn open_sudoers(path: &Path) -> io::Result<Vec<basic_parser::Parsed<Sudo>>> {
    super::super::open_sudoers(path).map(|text| parse_sudoers(&text))
}

#[cfg(feature = "unstable-remote-sudoers")]
fn open_remote_sudoers(
    path: &Path,
    peer: &PeerSpec,
) -> io::Result<Vec<basic_parser::Parsed<Sudo>>> {
    super::super::open_remote_sudoers(path, peer).map(|text| parse_sudoers(&text))
}

pub(super) fn specify_host_user_runas<User: UnixUser + PartialEq<User>>(
    this: &mut Sudoers,
    hostname: &system::Hostname,
    requesting_user: &User,
    target_user: Option<&User>,
) {
    let customisers = std::mem::take(&mut this.customisers.non_cmnd);

    let host_matcher = &match_token(hostname);
    let host_aliases = get_aliases(&this.aliases.host, host_matcher);

    let user_matcher = &match_user(requesting_user);
    let user_aliases = get_aliases(&this.aliases.user, user_matcher);

    let runas_matcher_aliases = target_user.map(|target_user| {
        let runas_matcher = match_user(target_user);
        let runas_aliases = get_aliases(&this.aliases.runas, &runas_matcher);

        (runas_matcher, runas_aliases)
    });

    let match_scope = |scope| match scope {
        ConfigScope::Generic => true,
        ConfigScope::Host(list) => find_item(&list, host_matcher, &host_aliases),
        ConfigScope::User(list) => find_item(&list, user_matcher, &user_aliases),
        ConfigScope::RunAs(list) => {
            runas_matcher_aliases
                .as_ref()
                .is_some_and(|(runas_matcher, runas_aliases)| {
                    find_item(&list, runas_matcher, runas_aliases)
                })
        }
        ConfigScope::Command(_list) => {
            unreachable!("command-specific defaults are filtered out")
        }
    };

    for (scope, modifiers) in customisers {
        if match_scope(scope) {
            for modifier in modifiers {
                modifier.apply(&mut this.settings);
            }
        }
    }
}

pub(super) fn specify_command(this: &mut Sudoers, command: &Path, arguments: &[OsString]) {
    let customisers = std::mem::take(&mut this.customisers.cmnd);

    let cmnd_matcher = &match_command((command, arguments));
    let cmnd_aliases = get_aliases(&this.aliases.cmnd, cmnd_matcher);

    for (scope, modifiers) in customisers {
        if find_item(&scope, cmnd_matcher, &cmnd_aliases) {
            for modifier in modifiers {
                modifier.apply(&mut this.settings);
            }
        }
    }
}

/// Process a sudoers-parsing file into a workable AST
pub(super) fn analyze(
    path: &Path,
    sudoers: impl IntoIterator<Item = basic_parser::Parsed<Sudo>>,
) -> (Sudoers, Vec<Error>) {
    use crate::common::{HARDENED_ENUM_VALUE_0, HARDENED_ENUM_VALUE_1, HARDENED_ENUM_VALUE_2};
    use Directive::*;

    let mut result: Sudoers = Default::default();

    /// The IncludeState allows to tell whether including new files is allowed.
    /// There are two situations:
    /// - inclusion is forbidden (as when the @socket directive is used)
    /// - inclusion is allowed but we need to ensure we didn't go beyond the limit
    #[derive(Clone, Copy)]
    #[repr(u32)]
    enum IncludeState {
        #[cfg(feature = "unstable-remote-sudoers")]
        Forbidden = HARDENED_ENUM_VALUE_0,
        Allowed(u8) = HARDENED_ENUM_VALUE_1,
    }

    impl IncludeState {
        #[inline]
        fn inc(&mut self) -> &mut Self {
            #[cfg_attr(
                not(feature = "unstable-remote-sudoers"),
                allow(irrefutable_let_patterns)
            )]
            if let IncludeState::Allowed(x) = self {
                *x += 1;
            }
            self
        }

        #[inline]
        fn limit_reached(&self) -> bool {
            match self {
                #[cfg(feature = "unstable-remote-sudoers")]
                IncludeState::Forbidden => true,
                IncludeState::Allowed(x) => *x >= INCLUDE_LIMIT,
            }
        }
    }

    /// The directive that produced the inclusion.
    #[repr(u32)]
    enum IncludeDirective {
        Include = HARDENED_ENUM_VALUE_0,
        IncludeDir = HARDENED_ENUM_VALUE_1,
        #[cfg(feature = "unstable-remote-sudoers")]
        Remote(PeerSpec) = HARDENED_ENUM_VALUE_2,
    }

    impl fmt::Display for IncludeDirective {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let s = match self {
                IncludeDirective::Include => "@include",
                IncludeDirective::IncludeDir => "@includedir",
                #[cfg(feature = "unstable-remote-sudoers")]
                IncludeDirective::Remote(_) => "@socket",
            };
            write!(f, "{s}")
        }
    }

    fn resolve_relative(base: &Path, path: impl AsRef<Path>) -> PathBuf {
        if path.as_ref().is_relative() {
            // there should always be a parent since we start with /etc/sudoers, and make every other path
            // absolute based on previous inputs; not having a parent is therefore a serious bug
            base.parent()
                .expect("invalid hardcoded path in sudo-rs")
                .join(path)
        } else {
            path.as_ref().into()
        }
    }

    struct IncludeContext<'a> {
        path: &'a Path,
        parent: &'a Path,
        span: Span,
        diagnostics: &'a mut Vec<Error>,
        include_state: &'a mut IncludeState,
        include_source: IncludeDirective,
    }

    fn include(cfg: &mut Sudoers, ctx: IncludeContext) {
        // IncludeState::limit_reached() will also detect forbidden includes
        if ctx.include_state.limit_reached() {
            let message = match ctx.include_state {
                IncludeState::Allowed(_) => {
                    format!(
                        "include file limit reached opening '{}'",
                        ctx.path.display()
                    )
                }
                #[cfg(feature = "unstable-remote-sudoers")]
                IncludeState::Forbidden => {
                    format!("{} forbidden at this stage", ctx.include_source)
                }
            };
            ctx.diagnostics.push(Error {
                source: Some(ctx.parent.to_owned()),
                location: Some(ctx.span),
                message,
            });
        } else {
            let (res, next_state, kind) = match ctx.include_source {
                #[cfg(feature = "unstable-remote-sudoers")]
                IncludeDirective::Remote(peer) => (
                    open_remote_sudoers(ctx.path, &peer),
                    &mut IncludeState::Forbidden,
                    "socket",
                ),
                _ => (open_sudoers(ctx.path), ctx.include_state.inc(), "file"),
            };

            match res {
                Ok(subsudoer) => process(cfg, ctx.path, subsudoer, ctx.diagnostics, next_state),
                Err(e) => {
                    let message = if e.kind() == io::ErrorKind::NotFound {
                        // improve the error message in this case
                        format!("cannot open sudoers {} '{}'", kind, ctx.path.display())
                    } else {
                        e.to_string()
                    };

                    ctx.diagnostics.push(Error {
                        source: Some(ctx.parent.to_owned()),
                        location: Some(ctx.span),
                        message,
                    })
                }
            }
        }
    }

    fn process(
        cfg: &mut Sudoers,
        cur_path: &Path,
        sudoers: impl IntoIterator<Item = basic_parser::Parsed<Sudo>>,
        diagnostics: &mut Vec<Error>,
        include_state: &mut IncludeState,
    ) {
        for item in sudoers {
            match item {
                Ok(line) => match line {
                    Sudo::LineComment => {}

                    Sudo::Spec(permission) => {
                        diagnostics.extend(get_ignored_tags(&permission).map(|span| Error {
                            source: Some(cur_path.to_owned()),
                            location: Some(span),
                            message: "this tag is ignored by sudo-rs".to_string(),
                        }));
                        cfg.rules.push(permission);
                    }

                    Sudo::Decl(HostAlias(mut def)) => cfg.aliases.host.1.append(&mut def),
                    Sudo::Decl(UserAlias(mut def)) => cfg.aliases.user.1.append(&mut def),
                    Sudo::Decl(RunasAlias(mut def)) => cfg.aliases.runas.1.append(&mut def),
                    Sudo::Decl(CmndAlias(mut def)) => cfg.aliases.cmnd.1.append(&mut def),

                    Sudo::Decl(Defaults(params, scope)) => {
                        if let ConfigScope::Command(specs) = scope {
                            cfg.customisers.cmnd.push((
                                specs
                                    .into_iter()
                                    .map(|spec| {
                                        spec.map(|simple_command| {
                                            (simple_command, Args::Prefix(Box::default()))
                                        })
                                    })
                                    .collect(),
                                params,
                            ));
                        } else {
                            cfg.customisers.non_cmnd.push((scope, params));
                        }
                    }

                    Sudo::Include(path, span) => include(
                        cfg,
                        IncludeContext {
                            path: &resolve_relative(cur_path, path),
                            parent: cur_path,
                            span,
                            diagnostics,
                            include_state,
                            include_source: IncludeDirective::Include,
                        },
                    ),

                    #[cfg(feature = "unstable-remote-sudoers")]
                    Sudo::Remote(path, peer_spec, span) => {
                        let socket_path = Path::new(&path);
                        if socket_path.is_relative() {
                            diagnostics.push(Error {
                                source: Some(cur_path.to_owned()),
                                location: Some(span),
                                message: format!(
                                    "cannot open socket {path}: path must be absolute"
                                ),
                            });
                        } else {
                            include(
                                cfg,
                                IncludeContext {
                                    path: socket_path,
                                    parent: cur_path,
                                    span,
                                    diagnostics,
                                    include_state,
                                    include_source: IncludeDirective::Remote(peer_spec),
                                },
                            );
                        }
                    }

                    Sudo::IncludeDir(path, span) => {
                        if path.contains("%h") {
                            diagnostics.push(Error {
                                source: Some(cur_path.to_owned()),
                                location: Some(span),
                                message: format!(
                                    "cannot open sudoers file {path}: \
                                     percent escape %h in includedir is unsupported"
                                ),
                            });
                            continue;
                        }

                        let path = resolve_relative(cur_path, path);
                        let Ok(files) = std::fs::read_dir(&path) else {
                            diagnostics.push(Error {
                                source: Some(cur_path.to_owned()),
                                location: Some(span),
                                message: format!("cannot open sudoers file {}", path.display()),
                            });
                            continue;
                        };
                        let mut safe_files = files
                            .filter_map(|direntry| {
                                let path = direntry.ok()?.path();
                                let text = path.file_name()?.to_str()?;
                                if text.ends_with('~') || text.contains('.') {
                                    None
                                } else {
                                    Some(path)
                                }
                            })
                            .collect::<Vec<_>>();
                        safe_files.sort();
                        for file in safe_files {
                            include(
                                cfg,
                                IncludeContext {
                                    path: file.as_ref(),
                                    parent: cur_path,
                                    span,
                                    diagnostics,
                                    include_state,
                                    include_source: IncludeDirective::IncludeDir,
                                },
                            )
                        }
                    }
                },

                Err(basic_parser::Status::Fatal(pos, kind)) => diagnostics.push(Error {
                    source: Some(cur_path.to_owned()),
                    location: Some(pos),
                    message: kind.to_string(),
                }),
                Err(_) => panic!("internal parser error"),
            }
        }
    }

    fn get_ignored_tags(
        PermissionSpec { permissions, .. }: &PermissionSpec,
    ) -> impl Iterator<Item = Span> + '_ {
        permissions
            .iter()
            .flat_map(|(_host, runas_cmds)| runas_cmds)
            .flat_map(|(_runas, CommandSpec(tags, _cmd))| tags)
            .flat_map(|modifier| {
                let mut tag = Tag::default();
                modifier.apply(&mut tag);
                tag.ignored
            })
    }

    let mut diagnostics = vec![];
    process(
        &mut result,
        path,
        sudoers,
        &mut diagnostics,
        &mut IncludeState::Allowed(0),
    );

    sanitize_alias_tables(&mut result.aliases, &mut diagnostics);

    (result, diagnostics)
}
