/* SPDX-License-Identifier: Apache-2.0 OR MIT */
/* Exercise sudoers' real private environment, without a sudo frontend. */
#include <config.h>

#include <locale.h>
#include <pwd.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include <sudoers.h>

#if defined(HAVE_PAM) || defined(HAVE_LOGIN_CAP_H) || !defined(_PATH_ENVIRONMENT)
# error "This fixture needs the Linux sudoers build without PAM or login classes"
#endif

/* An explicitly empty system environment, not the compute node's /etc/environment. */
static unsigned int system_env_reads;

static void *
empty_env_open(const char *path)
{
    if (strcmp(path, _PATH_ENVIRONMENT) != 0)
        return NULL;
    system_env_reads++;
    return &system_env_reads;
}

static void
empty_env_close(void *cookie)
{
    (void)cookie;
}

static char *
empty_env_next(void *cookie, int *error)
{
    (void)cookie;
    *error = 0;
    return NULL;
}

static char **
next_vector(char **first)
{
    for (char **p = first; *p != NULL; p++) {
        if (strcmp(*p, "--") == 0) {
            *p = NULL;
            return p + 1;
        }
    }
    return NULL;
}

int
main(int argc, char **argv)
{
    /* Shell, command and account strings are data; no NSS identity is adopted or command run. */
    struct passwd caller = {
        .pw_name = "caller", .pw_uid = 1000, .pw_gid = 1000,
        .pw_dir = "/home/caller", .pw_shell = "/bin/sh",
    };
    struct passwd target = {
        .pw_name = "target", .pw_uid = 1001, .pw_gid = 1001,
        .pw_dir = "/home/target", .pw_shell = "/bin/sh",
    };
    struct sudoers_context ctx = {
        .user = {
            .name = caller.pw_name, .pw = &caller, .uid = caller.pw_uid,
            .gid = caller.pw_gid, .cmnd = "/usr/bin/env",
        },
        .runas = { .pw = &target },
        .mode = MODE_RUN,
    };

    /* Private protocol: KEEP CHECK SECURE_PATH INHERITED... -- ASSIGNED... -- KEYS... */
    if (getuid() == 0 || getuid() != geteuid() || getgid() != getegid() || argc < 7)
        return 2;
    char **inherited = argv + 4;
    char **assigned = next_vector(inherited);
    char **keys = assigned == NULL ? NULL : next_vector(assigned);
    if (keys == NULL || *keys == NULL)
        return 2;
    ctx.user.envp = inherited;
    ctx.user.env_add = assigned;

    if (setlocale(LC_ALL, "C") == NULL || !sudoers_initlocale("C", "C") || !init_defaults())
        return 3;
    eventlog_set_type(0); /* Do not send validation diagnostics to a host log. */
    if (!set_default(&ctx, "env_reset", NULL, true, NULL, 0, 0, true) ||
        !set_default(&ctx, "env_keep", argv[1], true, NULL, 0, 0, true) ||
        !set_default(&ctx, "env_check", argv[2], true, NULL, 0, 0, true) ||
        !set_default(&ctx, "secure_path", *argv[3] ? argv[3] : NULL, *argv[3] != '\0',
            NULL, 0, 0, true) || def_exempt_group != NULL)
        return 3;

    register_env_file(empty_env_open, empty_env_close, empty_env_next, true);
    if (!env_init(inherited) || !rebuild_env(&ctx) || system_env_reads != 1)
        return 4;

    /* Match the real restricted assignment path's ordering, without checking any policy. */
    if (*assigned != NULL && !validate_env_vars(&ctx, assigned)) {
        puts("-\terror");
    } else {
        if (*assigned != NULL && !insert_env_vars(assigned))
            return 5;
        for (; *keys != NULL; keys++) {
            const char *value = sudo_getenv(*keys);
            if (value == NULL)
                printf("%s\tdrop\n", *keys);
            else
                printf("%s\tpresent\t%s\n", *keys, value);
        }
    }
    env_free();
    sudoers_gc_run();
    return fflush(stdout) == 0 ? 0 : 6;
}
