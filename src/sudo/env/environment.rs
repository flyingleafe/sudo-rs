use std::{
    collections::HashMap,
    ffi::{OsStr, OsString},
    os::unix::prelude::OsStrExt,
};

use crate::common::{CommandAndArguments, Context, Error, context::LaunchType};
use crate::sudoers::Restrictions;

use super::filter::{keep_inherited, should_keep};

// TODO: use _PATH_STDPATH from paths.h
pub(crate) const PATH_DEFAULT: &str = "/usr/bin:/bin:/usr/sbin:/sbin";

pub type Environment = HashMap<OsString, OsString>;

/// obtain the system environment
pub fn system_environment() -> Environment {
    std::env::vars_os().collect()
}

/// Formats the command and arguments passed for the SUDO_COMMAND
/// environment variable. Limit the length to 4096 bytes to prevent
/// execve failure for very long argument vectors
fn format_command(command_and_arguments: &CommandAndArguments) -> OsString {
    let mut formatted: OsString = command_and_arguments.command.clone().into();

    for arg in &command_and_arguments.arguments {
        if formatted.len() + arg.len() < 4096 {
            formatted.push(" ");
            formatted.push(arg);
        }
    }

    formatted
}

/// Construct sudo-specific environment variables
fn add_extra_env(
    context: &Context,
    cfg: &Restrictions,
    sudo_ps1: Option<OsString>,
    environment: &mut Environment,
) {
    // current user
    environment.insert("SUDO_COMMAND".into(), format_command(&context.command));
    environment.insert(
        "SUDO_UID".into(),
        context.current_user.uid.to_string().into(),
    );
    environment.insert(
        "SUDO_GID".into(),
        context.current_user.gid.to_string().into(),
    );
    environment.insert("SUDO_USER".into(), context.current_user.name.clone().into());
    environment.insert("SUDO_HOME".into(), context.current_user.home.clone().into());
    // The current SHELL variable should determine the shell to run when -s is passed, if none set use passwd entry
    environment
        .entry("SHELL".into())
        .or_insert_with(|| context.target_user.shell.clone().into());
    // HOME: Set to the home directory of the target user if -i or -H are specified, env_reset or always_set_home are
    // set in sudoers, or when the -s option is specified and set_home is set in sudoers.
    // In sudo-rs env_reset is mandatory, so we always set HOME unless it's in the env_keep list.
    environment
        .entry("HOME".into())
        .or_insert_with(|| context.target_user.home.clone().into());

    match (
        environment.get(OsStr::new("LOGNAME")),
        environment.get(OsStr::new("USER")),
    ) {
        // Set to the login name of the target user when the -i option is specified,
        // when the set_logname option is enabled in sudoers, or when the env_reset option
        // is enabled in sudoers (unless LOGNAME is present in the env_keep list).
        // Since we always want to do env_reset -> always set these except when present in env
        (None, None) => {
            environment.insert("LOGNAME".into(), context.target_user.name.clone().into());
            environment.insert("USER".into(), context.target_user.name.clone().into());
        }
        // LOGNAME should be set to the same value as USER if the latter is preserved.
        (None, Some(user)) => {
            environment.insert("LOGNAME".into(), user.clone());
        }
        // USER should be set to the same value as LOGNAME if the latter is preserved.
        (Some(logname), None) => {
            environment.insert("USER".into(), logname.clone());
        }
        (Some(_), Some(_)) => {}
    }

    // Overwrite PATH when secure_path is set
    if let Some(secure_path) = &cfg.path {
        // assign path by env path or secure_path configuration
        environment.insert("PATH".into(), secure_path.into());
    }
    // If the PATH and TERM variables are not preserved from the user's environment, they will be set to default value
    environment
        .entry("PATH".into())
        .or_insert_with(|| PATH_DEFAULT.into());
    // If the TERM variable is not preserved from the user's environment, it will be set to default value
    environment
        .entry("TERM".into())
        .or_insert_with(|| "unknown".into());
    // The SUDO_PS1 variable requires special treatment as the PS1 variable must be set in the
    // target environment to the same value of SUDO_PS1 if the latter is set.
    if let Some(sudo_ps1_value) = sudo_ps1 {
        // set PS1 to the SUDO_PS1 value in the target environment
        environment.insert("PS1".into(), sudo_ps1_value);
    }
}

/// Construct the final environment from the current one and a sudo context
/// see <https://github.com/sudo-project/sudo/blob/main/plugins/sudoers/env.c> for the original implementation
/// see <https://www.sudo.ws/docs/man/sudoers.man/#Command_environment> for the original documentation
///
/// The HOME, SHELL, LOGNAME and USER environment variables are initialized based on the target user
/// and the SUDO_* variables are set based on the invoking user.
///
/// Additional variables, such as DISPLAY, PATH and TERM, are preserved from the invoking user's
/// environment if permitted by the env_check, or env_keep options
///
/// If the PATH and TERM variables are not preserved from the user's environment, they will be set to default value
///
/// Environment variables with a value beginning with ‘()’ are removed
pub fn get_target_environment(
    current_env: Environment,
    additional_env: impl IntoIterator<Item = (OsString, OsString)>,
    user_override: Vec<(String, String)>,
    context: &Context,
    settings: &Restrictions,
) -> Result<Environment, Error> {
    // retrieve SUDO_PS1 value to set a PS1 value as additional environment
    let sudo_ps1 = current_env.get(OsStr::new("SUDO_PS1")).cloned();

    // variables preserved from the invoking user's environment by the
    // env_keep list take precedence over those in the PAM environment
    let mut environment: HashMap<_, _> = additional_env.into_iter().collect();

    // the policy decision per variable is `filter::keep_inherited` (on the bytes of name and
    // value); collecting and merging the maps stays here
    let login = context.launch == LaunchType::Login;
    environment.extend(current_env.into_iter().filter(|(key, value)| {
        keep_inherited(key.as_bytes(), value.as_bytes(), login, settings)
    }));

    add_extra_env(context, settings, sudo_ps1, &mut environment);

    let mut rejected_vars = Vec::new();
    for (key, value) in user_override {
        if should_keep(key.as_bytes(), value.as_bytes(), settings) {
            environment.insert(key.into(), value.into());
        } else {
            rejected_vars.push(key);
        }
    }
    if !rejected_vars.is_empty() {
        return Err(Error::EnvironmentVar(rejected_vars));
    }

    Ok(environment)
}

/// Extend the environment with user-supplied info
pub fn dangerous_extend<S>(env: &mut Environment, user_override: impl IntoIterator<Item = (S, S)>)
where
    S: Into<OsString>,
{
    env.extend(
        user_override
            .into_iter()
            .map(|(key, value)| (key.into(), value.into())),
    )
}
