//! Input format shared by `sudoers_decide` and `sudoers_defaults`:
//!
//! ```text
//! <invoking user>:<target user>:<target group>:<host>\n
//! <command> <argument>...\n
//! <policy text>
//! ```
//!
//! A user is `name` or `name/group,group,...` (supplementary groups); a group is `name` or
//! `#gid`. Ids are derived from names as the sudoers unit tests derive them (`dummy_cksum` in
//! `src/sudoers/test/mod.rs`: root is 0, other names 1000..2360), so that test policies with
//! `#id` entries keep their meaning, and a user's primary group has the user's name and id.

use std::ffi::OsString;
use std::path::PathBuf;

use sudo_rs::fuzz_api::{DecisionInput, FuzzGroup, FuzzUser};

pub fn test_id(name: &str) -> u32 {
    if name == "root" {
        0
    } else {
        1000 + name.chars().fold(0u64, |x, y| (x * 97 + y as u64) % 1361) as u32
    }
}

fn group(spec: &str) -> FuzzGroup {
    match spec.strip_prefix('#').map(str::parse::<u32>) {
        Some(Ok(gid)) => FuzzGroup { name: None, gid },
        _ => FuzzGroup {
            name: Some(spec.to_owned()),
            gid: test_id(spec),
        },
    }
}

fn user(spec: &str) -> FuzzUser {
    let (name, groups) = spec.split_once('/').unwrap_or((spec, ""));
    FuzzUser {
        name: name.to_owned(),
        uid: test_id(name),
        primary: FuzzGroup {
            name: Some(name.to_owned()),
            gid: test_id(name),
        },
        supplementary: groups.split(',').filter(|g| !g.is_empty()).map(group).collect(),
    }
}

pub fn decision_input(data: &[u8]) -> Option<DecisionInput> {
    let text = std::str::from_utf8(data).ok()?;
    let (header, rest) = text.split_once('\n')?;
    let (command, policy) = rest.split_once('\n').unwrap_or((rest, ""));

    let mut fields = header.splitn(4, ':');
    let invoking_user = user(fields.next()?);
    let target_user = user(fields.next().unwrap_or("root"));
    let target_group = match fields.next() {
        Some(g) if !g.is_empty() => group(g),
        _ => target_user.primary.clone(),
    };
    let hostname = fields.next().unwrap_or("server").to_owned();

    let mut words = command.split_whitespace();
    let command = PathBuf::from(words.next().unwrap_or("/bin/true"));
    let arguments = words.map(OsString::from).collect();

    Some(DecisionInput {
        policy: policy.to_owned(),
        hostname,
        invoking_user,
        target_user,
        target_group,
        command,
        arguments,
    })
}

/// `in_group` of `src/sudoers/mod.rs` for the fuzzed users
#[allow(dead_code)] // used by one of the two targets that include this module
pub fn in_group(user: &FuzzUser, group: &FuzzGroup) -> bool {
    std::iter::once(&user.primary)
        .chain(&user.supplementary)
        .any(|g| g.gid == group.gid)
}
