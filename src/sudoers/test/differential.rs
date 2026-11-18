//! Harness for the differential test in `proofs/differential`: runs the real sudoers parser
//! (`Sudoers::read`) and the real decision (`Sudoers::check`) on every case of the file named
//! by `SUDO_DIFF_CASES` and writes one verdict line per case to the file named by
//! `SUDO_DIFF_OUT`. Without `SUDO_DIFF_CASES` the test does nothing.
//!
//! The users and groups of a case come from its own passwd/group lines; the fake `UnixUser`
//! and `UnixGroup` below behave like `impl UnixUser for User` and `impl UnixGroup for Group`
//! (`src/system/interface.rs`) over that database, and the target user and group are derived
//! from the `-u`/`-g` flags as `resolve_target_user_and_group` (`src/common/resolve.rs`) does.

use std::ffi::{CStr, OsString};
use std::fmt::Write as _;
use std::path::Path;

use super::super::*;

#[derive(PartialEq)]
struct DbGroup {
    name: String,
    gid: GroupId,
}

/// A passwd entry with its group vector (primary gid, then every group listing it).
#[derive(PartialEq)]
struct DbUser<'a> {
    name: String,
    uid: UserId,
    gid: GroupId,
    groups: Vec<GroupId>,
    db: &'a [DbGroup],
}

/// `Group { gid, name }` as `Group::from_name` / `Group::from_gid` return it.
struct DbGroupRef {
    gid: GroupId,
    name: Option<String>,
}

impl UnixUser for DbUser<'_> {
    fn has_name(&self, name: &str) -> bool {
        self.name == name
    }
    fn has_uid(&self, uid: UserId) -> bool {
        self.uid == uid
    }
    fn is_root(&self) -> bool {
        self.has_uid(UserId::ROOT)
    }
    fn in_group_by_name(&self, name: &CStr) -> bool {
        // `Group::from_name` (getgrnam: the first entry with that name), then by gid
        match self.db.iter().find(|g| g.name.as_bytes() == name.to_bytes()) {
            Some(group) => self.in_group_by_gid(group.gid),
            None => false,
        }
    }
    fn in_group_by_gid(&self, gid: GroupId) -> bool {
        self.groups.contains(&gid)
    }
    type Group = DbGroupRef;
    fn group(&self) -> DbGroupRef {
        DbGroupRef {
            gid: self.gid,
            name: None,
        }
    }
}

impl UnixGroup for DbGroupRef {
    fn as_gid(&self) -> GroupId {
        self.gid
    }
    fn try_as_name(&self) -> Option<&str> {
        self.name.as_deref()
    }
}

/// One case record (format: `proofs/differential/Differential/Case.lean`).
#[derive(Default)]
struct Record {
    index: String,
    passwd: Vec<String>,
    group: Vec<String>,
    host: String,
    user: String,
    runas: Vec<String>,
    command: Vec<String>,
    sudoers: Vec<String>,
}

fn parse_records(text: &str) -> Vec<Record> {
    let mut out = Vec::new();
    let mut cur = Record::default();
    for line in text.lines() {
        let (key, rest) = line.split_once(' ').unwrap_or((line, ""));
        match key {
            "case" => cur.index = rest.to_string(),
            "passwd" => cur.passwd.push(rest.to_string()),
            "group" => cur.group.push(rest.to_string()),
            "host" => cur.host = rest.to_string(),
            "user" => cur.user = rest.to_string(),
            "runas" => cur.runas = rest.split_whitespace().map(String::from).collect(),
            "command" => cur.command = rest.split_whitespace().map(String::from).collect(),
            "sudoers" => cur.sudoers.push(rest.to_string()),
            "end" => out.push(std::mem::take(&mut cur)),
            _ => {}
        }
    }
    out
}

fn show_tag(tag: &Tag) -> String {
    let auth = match tag.authenticate {
        Authenticate::None => "none",
        Authenticate::Passwd => "passwd",
        Authenticate::Nopasswd => "nopasswd",
    };
    let env = match tag.env {
        EnvironmentControl::Implicit => "implicit",
        EnvironmentControl::Setenv => "setenv",
        EnvironmentControl::Nosetenv => "nosetenv",
    };
    let exec = match tag.noexec {
        ExecControl::Implicit => "implicit",
        ExecControl::Exec => "exec",
        ExecControl::Noexec => "noexec",
    };
    let set = |b: bool| if b { "set" } else { "none" };
    format!(
        "allow auth={auth} env={env} exec={exec} cwd={} apparmor={}",
        set(tag.cwd.is_some()),
        set(tag.apparmor_profile.is_some())
    )
}

fn verdict(rec: &Record) -> String {
    let groups: Vec<DbGroup> = rec
        .group
        .iter()
        .map(|l| {
            let f: Vec<&str> = l.split(':').collect();
            DbGroup {
                name: f[0].to_string(),
                gid: GroupId::new(f[2].parse().unwrap()),
            }
        })
        .collect();
    let members: Vec<(GroupId, Vec<&str>)> = rec
        .group
        .iter()
        .map(|l| {
            let f: Vec<&str> = l.split(':').collect();
            let m = f[3].split(',').filter(|s| !s.is_empty()).collect();
            (GroupId::new(f[2].parse().unwrap()), m)
        })
        .collect();
    let users: Vec<DbUser> = rec
        .passwd
        .iter()
        .map(|l| {
            let f: Vec<&str> = l.split(':').collect();
            let gid = GroupId::new(f[3].parse().unwrap());
            let mut gids = vec![gid];
            gids.extend(
                members
                    .iter()
                    .filter(|(_, m)| m.contains(&f[0]))
                    .map(|(g, _)| *g),
            );
            DbUser {
                name: f[0].to_string(),
                uid: UserId::new(f[2].parse().unwrap()),
                gid,
                groups: gids,
                db: &groups,
            }
        })
        .collect();

    let user_named = |n: &str| users.iter().find(|u| u.name == n);
    let group_ref = |g: &DbGroup| DbGroupRef {
        gid: g.gid,
        name: Some(g.name.clone()),
    };
    let group_named = |n: &str| groups.iter().find(|g| g.name == n).map(group_ref);
    let group_with_gid = |gid: GroupId| groups.iter().find(|g| g.gid == gid).map(group_ref);

    let Some(am_user) = user_named(&rec.user) else {
        return "error unknown invoking user".into();
    };
    let flag = |f: &str| {
        rec.runas
            .iter()
            .position(|x| x == f)
            .map(|i| rec.runas[i + 1].as_str())
    };
    // resolve_target_user_and_group
    let target = match (flag("-u"), flag("-g")) {
        (None, Some(g)) => Some(am_user).zip(group_named(g)),
        (Some(u), None) => user_named(u).and_then(|u| Some(u).zip(group_with_gid(u.gid))),
        (None, None) => user_named("root").zip(group_named("root")),
        (Some(u), Some(g)) => user_named(u).zip(group_named(g)),
    };
    let Some((target_user, target_group)) = target else {
        return "error unresolved target".into();
    };

    let text = rec.sudoers.join("\n") + "\n";
    let (mut sudoers, errors) = Sudoers::read(text.as_bytes(), "/etc/sudoers").unwrap();
    if !errors.is_empty() {
        let msgs: Vec<String> = errors.iter().map(|e| e.message.clone()).collect();
        return format!("error {}", msgs.join("; "));
    }

    let arguments: Vec<OsString> = rec.command[1..].iter().map(OsString::from).collect();
    let judgement = sudoers.check(
        am_user,
        &system::Hostname::fake(&rec.host),
        Request {
            user: target_user,
            group: &target_group,
            command: Path::new(&rec.command[0]),
            arguments: &arguments,
        },
    );
    match judgement.flags {
        Some(tag) => show_tag(&tag),
        None => "deny".into(),
    }
}

#[test]
fn differential_cases() {
    let Ok(cases) = std::env::var("SUDO_DIFF_CASES") else {
        return;
    };
    let out = std::env::var("SUDO_DIFF_OUT").expect("SUDO_DIFF_OUT must name the output file");
    let text = std::fs::read_to_string(cases).unwrap();
    let mut result = String::new();
    for rec in parse_records(&text) {
        writeln!(result, "{} {}", rec.index, verdict(&rec)).unwrap();
    }
    std::fs::write(out, result).unwrap();
}
