use crate::system::interface::UserId;
use crate::system::{Group, User};
use core::fmt;
use std::{
    env,
    ffi::CStr,
    fs, io, ops,
    os::unix::prelude::MetadataExt,
    path::{Path, PathBuf},
    str::FromStr,
};

use super::SudoString;
use super::{Error, context::LaunchType};

#[derive(PartialEq, Debug)]
enum NameOrId<'a, T: FromStr> {
    Name(&'a SudoString),
    Id(T),
}

impl<'a, T: FromStr> NameOrId<'a, T> {
    pub fn parse(input: &'a SudoString) -> Option<Self> {
        if input.is_empty() {
            None
        } else if let Some(stripped) = input.strip_prefix('#') {
            stripped.parse::<T>().ok().map(|id| Self::Id(id))
        } else {
            Some(Self::Name(input))
        }
    }
}

/// Fuzzing entry point: `NameOrId::parse` with user ids, as `resolve_target_user_and_group`
/// applies it to `-u`.
#[cfg(fuzzing)]
pub(crate) fn fuzz_name_or_id(input: &SudoString) -> Option<crate::fuzz_api::NameOrId> {
    NameOrId::<UserId>::parse(input).map(|parsed| match parsed {
        NameOrId::Name(name) => crate::fuzz_api::NameOrId::Name(name.as_str().to_owned()),
        NameOrId::Id(id) => crate::fuzz_api::NameOrId::Id(id.inner()),
    })
}

#[derive(Clone)]
pub struct CurrentUser {
    inner: User,
}

impl From<CurrentUser> for User {
    fn from(value: CurrentUser) -> Self {
        value.inner
    }
}

impl fmt::Debug for CurrentUser {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CurrentUser").field(&self.inner).finish()
    }
}

impl ops::Deref for CurrentUser {
    type Target = User;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl CurrentUser {
    #[cfg(any(test, kani))]
    pub fn fake(user: User) -> Self {
        Self { inner: user }
    }

    pub fn resolve() -> Result<Self, Error> {
        let mut cur_user = User::real()?.ok_or(Error::UserNotFound("current user".to_string()))?;
        // the current user can also have groups that are defined at runtime, so fetch the dynamic groups
        cur_user.groups = User::real_groups()?;
        Ok(Self { inner: cur_user })
    }
}

#[derive(Clone, Debug)]
pub struct AuthUser(User);

impl AuthUser {
    pub fn from_current_user(user: CurrentUser) -> Self {
        Self(user.inner)
    }

    pub fn resolve_root_for_rootpw() -> Result<Self, Error> {
        Ok(Self(
            User::from_uid(UserId::ROOT)?.ok_or(Error::UserNotFound("root".to_string()))?,
        ))
    }

    pub fn from_user_for_targetpw(user: User) -> Self {
        Self(user)
    }
}

impl ops::Deref for AuthUser {
    type Target = User;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

type Shell = Option<PathBuf>;

pub(super) fn resolve_shell(
    launch_type: LaunchType,
    current_user: &User,
    target_user: &User,
) -> Shell {
    match launch_type {
        LaunchType::Login => Some(target_user.shell.clone()),

        LaunchType::Shell => Some(
            env::var("SHELL")
                .map(|s| s.into())
                .unwrap_or_else(|_| current_user.shell.clone()),
        ),

        LaunchType::Direct => None,
    }
}

pub(crate) fn resolve_target_user_and_group(
    target_user_name_or_id: &Option<SudoString>,
    target_group_name_or_id: &Option<SudoString>,
    current_user: &CurrentUser,
) -> Result<(User, Group), Error> {
    // resolve user name or #<id> to a user
    let mut target_user =
        resolve_from_name_or_id(target_user_name_or_id, User::from_name, User::from_uid)?;

    // resolve group name or #<id> to a group
    let mut target_group =
        resolve_from_name_or_id(target_group_name_or_id, Group::from_name, Group::from_gid)?;

    match target_fallback(target_user_name_or_id.is_some(), target_group_name_or_id.is_some()) {
        // when -g is specified, but -u is not specified default -u to the current user
        TargetFallback::CurrentUser => {
            target_user = Some(current_user.clone().into());
        }
        // when -u is specified but -g is not specified, default -g to the primary group of the specified user
        TargetFallback::PrimaryGroupIfFound => {
            if let Some(user) = &target_user {
                target_group = Some(user.primary_group()?);
            }
        }
        // when no -u or -g is specified, default to root:root
        TargetFallback::Root => {
            target_user = User::from_name(c"root")?;
            target_group = Group::from_name(if cfg!(target_os = "linux") {
                c"root"
            } else {
                c"wheel"
            })?;
        }
        TargetFallback::Keep => {}
    }

    select_target(target_user, target_group).map_err(|missing| match missing {
        // group name or id not found
        TargetMissing::Group => Error::GroupNotFound(
            target_group_name_or_id
                .as_deref()
                .unwrap_or_default()
                .to_string(),
        ),
        // user (and maybe group) name or id not found
        TargetMissing::User => Error::UserNotFound(
            target_user_name_or_id
                .as_deref()
                .unwrap_or_default()
                .to_string(),
        ),
    })
}

/// How [resolve_target_user_and_group] completes the target pair once the user and the group
/// that `-u` and `-g` name have been looked up.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TargetFallback {
    /// Keep the results of the `-u`/`-g` lookups: both options given.
    Keep,
    /// `-g` without `-u`: the invoking user.
    CurrentUser,
    /// `-u` without `-g`: look up the primary group only if the user was found.
    PrimaryGroupIfFound,
    /// Neither option: `root` and the root group (`wheel` outside Linux), looked up by name.
    Root,
}

/// The completion step of [resolve_target_user_and_group], from whether `-u` and `-g` were
/// given. A pure decision: the lookups it selects are made by the caller.
fn target_fallback(user_given: bool, group_given: bool) -> TargetFallback {
    if user_given {
        if group_given {
            TargetFallback::Keep
        } else {
            TargetFallback::PrimaryGroupIfFound
        }
    } else if group_given {
        TargetFallback::CurrentUser
    } else {
        TargetFallback::Root
    }
}

/// The part of the target pair that [select_target] reports missing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TargetMissing {
    User,
    Group,
}

/// The last step of [resolve_target_user_and_group]: the pair if both parts are present,
/// otherwise the missing part, the user before the group.
fn select_target<U, G>(user: Option<U>, group: Option<G>) -> Result<(U, G), TargetMissing> {
    match (user, group) {
        (Some(user), Some(group)) => Ok((user, group)),
        (Some(_), None) => Err(TargetMissing::Group),
        _ => Err(TargetMissing::User),
    }
}

fn resolve_from_name_or_id<T, I, E>(
    input: &Option<SudoString>,
    from_name: impl FnOnce(&CStr) -> Result<Option<T>, E>,
    from_id: impl FnOnce(I) -> Result<Option<T>, E>,
) -> Result<Option<T>, E>
where
    I: FromStr,
{
    match input.as_ref().and_then(NameOrId::parse) {
        Some(NameOrId::Name(name)) => from_name(name.as_cstr()),
        Some(NameOrId::Id(id)) => from_id(id),
        None => Ok(None),
    }
}

/// Check whether a path points to a regular file and any executable flag is set
pub(crate) fn is_valid_executable(path: &Path) -> bool {
    if path.is_file() {
        match fs::metadata(path) {
            Ok(meta) => meta.mode() & 0o111 != 0,
            _ => false,
        }
    } else {
        false
    }
}

/// Resolve a executable name based in the PATH environment variable
/// When resolving a path, this code checks whether the target file is
/// a regular file and has any executable bits set. It does not specifically
/// check for user, group, or others' executable bit.
pub(crate) fn resolve_path(command: &Path, path: &str) -> Option<PathBuf> {
    // Depending on the security policy, the user's PATH environment variable may be modified,
    // replaced, or passed unchanged to the program that sudo executes.

    path.split(':')
        .map(Path::new)
        // ignore all relative paths ("", "." or "./")
        .filter(|path| path.is_absolute())
        // construct a possible executable absolute path candidate
        .map(|path| path.join(command))
        // check whether the candidate is a regular file and any executable flag is set
        .find(|arg| is_valid_executable(arg))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::common::resolve::CurrentUser;
    use crate::system::ROOT_GROUP_NAME;

    use super::{
        NameOrId, TargetFallback, TargetMissing, is_valid_executable, resolve_path,
        resolve_target_user_and_group, select_target, target_fallback,
    };

    #[test]
    fn target_selection_cases() {
        assert_eq!(target_fallback(false, false), TargetFallback::Root);
        assert_eq!(target_fallback(false, true), TargetFallback::CurrentUser);
        assert_eq!(target_fallback(true, false), TargetFallback::PrimaryGroupIfFound);
        assert_eq!(target_fallback(true, true), TargetFallback::Keep);

        // An ordinary synthetic account and group; no policy checks or NSS changes.
        let user = Some(1000u32);
        let group = Some(1001u32);
        assert_eq!(select_target(user, group), Ok((1000, 1001)));
        assert_eq!(select_target(user, None::<u32>), Err(TargetMissing::Group));
        assert_eq!(select_target(None::<u32>, group), Err(TargetMissing::User));
        assert_eq!(select_target(None::<u32>, None::<u32>), Err(TargetMissing::User));
    }

    #[test]
    fn test_resolve_path() {
        // Assume any linux distro has utilities in this PATH
        let path = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin";

        assert!(is_valid_executable(
            &resolve_path(Path::new("yes"), path).unwrap()
        ));

        assert!(is_valid_executable(
            &resolve_path(Path::new("whoami"), path).unwrap()
        ));

        assert!(is_valid_executable(
            &resolve_path(Path::new("env"), path).unwrap()
        ));
        assert_eq!(resolve_path(Path::new("thisisnotonyourfs"), path), None);
        assert_eq!(resolve_path(Path::new("thisisnotonyourfs"), "."), None);
    }

    #[test]
    fn test_name_or_id() {
        assert_eq!(NameOrId::<u32>::parse(&"".into()), None);
        assert_eq!(
            NameOrId::<u32>::parse(&"mies".into()),
            Some(NameOrId::Name(&"mies".into()))
        );
        assert_eq!(
            NameOrId::<u32>::parse(&"1337".into()),
            Some(NameOrId::Name(&"1337".into()))
        );
        assert_eq!(
            NameOrId::<u32>::parse(&"#1337".into()),
            Some(NameOrId::Id(1337))
        );
        assert_eq!(NameOrId::<u32>::parse(&"#-1".into()), None);
    }

    #[test]
    fn test_resolve_target_user_and_group() {
        let current_user = CurrentUser::resolve().unwrap();

        // fallback to root
        let (user, group) = resolve_target_user_and_group(&None, &None, &current_user).unwrap();
        assert_eq!(user.name, "root");
        assert_eq!(group.name.unwrap(), ROOT_GROUP_NAME);

        // unknown user
        let result =
            resolve_target_user_and_group(&Some("non_existing_ghost".into()), &None, &current_user);
        assert!(result.is_err());

        // unknown user
        let result =
            resolve_target_user_and_group(&None, &Some("non_existing_ghost".into()), &current_user);
        assert!(result.is_err());

        // fallback to current user when different group specified
        let (user, group) =
            resolve_target_user_and_group(&None, &Some(ROOT_GROUP_NAME.into()), &current_user)
                .unwrap();
        assert_eq!(user.name, current_user.name);
        assert_eq!(group.name.unwrap(), ROOT_GROUP_NAME);

        // fallback to current users group when no group specified
        let (user, group) =
            resolve_target_user_and_group(&Some(current_user.name.clone()), &None, &current_user)
                .unwrap();
        assert_eq!(user.name, current_user.name);
        assert_eq!(group.gid, current_user.gid);
    }
}

/// Resolve symlinks in all the directories leading up to a file, but
/// not the file itself; this allows sudo to specify a precise policy with
/// tools like busybox or pgrep (which is a symlink to pgrep on systems)
/// This function will check for existence.
pub fn canonicalize<P: AsRef<Path>>(path: P) -> io::Result<PathBuf> {
    let reconstructed_path = canonicalize_newfile(path)?;

    // access the object to generate the regular error if it does not exist
    let _ = fs::metadata(&reconstructed_path)?;

    Ok(reconstructed_path)
}

/// Resolve symlinks in all the directories leading up to a file, but
/// not the file itself; this allows us to keep symlinks as is, and will
/// also work on non-existing files.
pub fn canonicalize_newfile<P: AsRef<Path>>(path: P) -> io::Result<PathBuf> {
    let path = path.as_ref();
    let Some(parent) = path.parent() else {
        // path is "/" or a prefix
        return Ok(path.to_path_buf());
    };

    let canon_path = fs::canonicalize(parent)?;

    let reconstructed_path = if let Some(file_name) = path.file_name() {
        canon_path.join(file_name)
    } else {
        canon_path
    };

    Ok(reconstructed_path)
}

#[cfg(test)]
mod test {
    use super::canonicalize;
    use std::path::Path;

    #[test]
    fn canonicalization() {
        assert_eq!(canonicalize("/").unwrap(), Path::new("/"));
        assert!(canonicalize("").is_err());
        if cfg!(any(target_os = "linux")) {
            // this test REQUIRES /usr/bin/unxz to be a symlink for /usr/bin/xz or /usr/bin/busybox
            assert!(Path::new("/bin").is_symlink());
            assert!(Path::new("/usr/bin/unxz").is_symlink());
            assert_eq!(
                canonicalize("/usr/bin/unxz").unwrap(),
                Path::new("/usr/bin/unxz")
            );
            // this assumes /bin is a symlink on /usr/bin, like it is on modern Debian/Ubuntu
            assert_eq!(
                canonicalize("/bin/unxz").unwrap(),
                Path::new("/usr/bin/unxz")
            );
        } else if cfg!(target_os = "freebsd") {
            // this test REQUIRES /usr/bin/pkill to be a symlink
            assert!(Path::new("/usr/bin/pkill").is_symlink());
            assert_eq!(
                canonicalize("/usr/bin/pkill").unwrap(),
                Path::new("/usr/bin/pkill")
            );
            assert_eq!(canonicalize("/bin/pkill").unwrap(), Path::new("/bin/pkill"));
        } else {
            panic!(
                "canonicalization test not yet adapted for {}",
                std::env::consts::OS
            );
        }
    }
}
