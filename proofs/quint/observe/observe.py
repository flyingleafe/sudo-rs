#!/usr/bin/env python3
"""Runs of the real sudo-rs binary checked against the Quint lifecycle model.

usage:
  observe.py record CAPTURE_DIR OUT.obs.json   turn a guest capture into an observation
  observe.py replay OBS.obs.json...            re-derive each observation from its raw
                                               capture and replay it through replay.qnt
  observe.py controls OBS.obs.json             negative controls on a real observation
  observe.py selftest                          harness check without any observation

CAPTURE_DIR is the /out directory written by guest-run.sh (copied out of the guest).
`record` is unprivileged and only reads it. An observation file holds the raw capture
verbatim, the provenance, and the facts derived from the raw capture. `replay` never trusts
the derived section: it derives again from the raw capture, rejects the file if the two
differ, and gives the model the re-derived facts. The policy verdict of each request comes
from the committed fixture (fixture/scenarios), never from the observation.

Exit status: 0 when every observation (or control) behaved as required, 1 otherwise,
2 on a usage error. Python 3.9+, standard library only; replay, controls and selftest need
`quint` on PATH (or in $QUINT). README.md ("Observed traces") documents the boundary.
"""

import copy
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
QUINT_DIR = os.path.dirname(HERE)
REPO = os.path.dirname(os.path.dirname(QUINT_DIR))
FIXTURE = os.path.join(HERE, "fixture")
MODEL_FILES = ("types.qnt", "kernel.qnt", "policy.qnt", "sudo.qnt", "replay.qnt")
FORMAT = "lifecycle-trace/1"
KIND_REAL = "real-binary-guest-capture"
ENVIRONMENT = "env -i PATH=/usr/bin:/bin"
INVOKER = "ferris"
REFUSAL = "sudo: I'm sorry %s. I'm afraid I can't do that\n" % INVOKER
# Fixture accounts -> account constants of types.qnt (ROOT, ALICE, BOB).
ACCOUNTS = {"root": 0, "ferris": 1, "another_user": 2}
NOT_RUN = "none"  # execCmd of a refused run (not a member of COMMANDS)
CRED_FIELDS = ("ruid", "euid", "suid", "rgid", "egid", "sgid", "groups")
SETID = ("setgroups", "setuid", "setgid", "setreuid", "setregid", "setresuid", "setresgid")
FORKS = ("clone", "clone3", "fork", "vfork")


class Reject(Exception):
    """The observation cannot be replayed; the message says why."""


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_text(text):
    return sha256_bytes(text.encode("utf-8"))


def sha256_file(path):
    with open(path, "rb") as f:
        return sha256_bytes(f.read())


def read_text(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


# ---- fixture ---------------------------------------------------------------------------


def committed_fixture():
    files = {name: read_text(os.path.join(FIXTURE, name)) for name in ("sudoers", "pam.d-sudo", "scenarios")}
    files["guest-run.sh"] = read_text(os.path.join(HERE, "guest-run.sh"))
    return files


def parse_scenarios(text):
    """name -> {verdict, model_cmd, argv}; the verdicts are pinned here, before any run."""
    scenarios = {}
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        name, verdict, model_cmd, *argv = line.split()
        scenarios[name] = {"verdict": verdict, "model_cmd": model_cmd, "argv": argv}
    return scenarios


def stock_pam_d_sudo():
    """STOCK_PAM_D_SUDO of the compliance framework, which the fixture reuses."""
    path = os.path.join(REPO, "test-framework", "sudo-test", "src", "constants.rs")
    m = re.search(r'pub const STOCK_PAM_D_SUDO: &str = "((?:[^"\\]|\\.)*)";', read_text(path))
    if not m:
        raise Reject("STOCK_PAM_D_SUDO not found in %s" % path)
    return m.group(1).replace("\\n", "\n")


# ---- raw capture helpers -------------------------------------------------------------------


def need(raw, key):
    if key not in raw:
        raise Reject("capture lacks %s" % key)
    return raw[key]


def parse_sums(text):
    sums = {}
    for line in text.splitlines():
        digest, _, name = line.partition("  ")
        sums[name] = digest
    return sums


def check_source(commit, tar_sha):
    """src.tar against `git archive` of the recorded commit, when the clone has it."""
    try:
        subprocess.run(["git", "-C", REPO, "cat-file", "-e", commit + "^{commit}"],
                       check=True, capture_output=True)
    except (OSError, subprocess.CalledProcessError):
        return "src.tar not rechecked: commit %s is not in this clone" % commit
    data = subprocess.run(["git", "-C", REPO, "archive", "--format=tar", commit],
                          check=True, capture_output=True).stdout
    if sha256_bytes(data) != tar_sha:
        raise Reject("src.tar is not `git archive` of the recorded commit %s" % commit)
    return "src.tar equals `git archive --format=tar %s`" % commit


def parse_identity(raw):
    users, groups, supp = {}, {}, {}
    for line in need(raw, "meta/passwd").splitlines():
        f = line.split(":")
        users[f[0]] = (int(f[2]), int(f[3]))
    for line in need(raw, "meta/group").splitlines():
        f = line.split(":")
        groups[f[0]] = int(f[2])
    for line in need(raw, "meta/groups").splitlines():
        name, *gids = line.split()
        supp[name] = sorted(int(g) for g in gids)
    uid_map, gid_map = {}, {}
    for name, abstract in ACCOUNTS.items():
        if name not in users:
            raise Reject("account %s missing from the capture" % name)
        uid, gid = users[name]
        if name == "root" and (uid, gid) != (0, 0):
            raise Reject("root is not uid 0 / gid 0")
        if name != "root" and (groups.get(name) != gid or supp.get(name) != [gid]):
            raise Reject("account %s is outside the model universe: its only group must be "
                         "its own primary group" % name)
        if uid in uid_map or gid in gid_map:
            raise Reject("fixture accounts share an id")
        uid_map[uid] = abstract
        gid_map[gid] = abstract
    return users, uid_map, gid_map


def amap(mapping, value, what):
    if value not in mapping:
        raise Reject("%s %d is not an id of a fixture account" % (what, value))
    return mapping[value]


def parse_status(text, what):
    fields = {}
    for line in text.splitlines():
        key, _, value = line.partition(":")
        fields[key] = value.split()
    try:
        uid = [int(x) for x in fields["Uid"]]
        gid = [int(x) for x in fields["Gid"]]
        return {
            "name": fields["Name"][0],
            "creds": {"ruid": uid[0], "euid": uid[1], "suid": uid[2],
                      "rgid": gid[0], "egid": gid[1], "sgid": gid[2],
                      "groups": sorted(int(x) for x in fields.get("Groups", []))},
            "fsuid": uid[3], "fsgid": gid[3],
            "CapEff": fields.get("CapEff", ["?"])[0],
            "NoNewPrivs": fields.get("NoNewPrivs", ["?"])[0],
        }
    except (KeyError, ValueError, IndexError):
        raise Reject("%s is not a /proc/<pid>/status listing" % what)


def abstract_creds(c, uid_map, gid_map, what):
    out = {k: amap(uid_map, c[k], what + " " + k) for k in ("ruid", "euid", "suid")}
    out.update({k: amap(gid_map, c[k], what + " " + k) for k in ("rgid", "egid", "sgid")})
    out["groups"] = sorted({amap(gid_map, g, what + " group") for g in c["groups"]})
    return out


def ticket_owners(text, uid_map, what):
    lines = [line for line in text.splitlines() if line.strip()]
    if lines == ["ABSENT"]:
        return []
    owners = set()
    for line in lines:
        if not line.isdigit():
            raise Reject("%s: unexpected entry %r in the timestamp directory" % (what, line))
        owners.add(amap(uid_map, int(line), what + ": timestamp file of uid"))
    return sorted(owners)


# ---- strace ---------------------------------------------------------------------------


def parse_strace(text):
    """[(pid, call, args, ret)] in the order the calls started."""
    events, pending = [], {}
    for line in text.splitlines():
        m = re.match(r"^(\d+)\s+(.*)$", line)
        if not m:
            raise Reject("unparsed strace line %r" % line)
        pid, rest = int(m.group(1)), m.group(2)
        if rest.startswith("+++") or rest.startswith("---"):
            continue
        if rest.endswith("<unfinished ...>"):
            pending[pid] = (len(events), rest[: -len("<unfinished ...>")].rstrip())
            events.append(None)
            continue
        resumed = re.match(r"^<\.\.\. \w+ resumed>(.*)$", rest)
        slot = None
        if resumed:
            if pid not in pending:
                raise Reject("strace resumes a call of process %d that never started" % pid)
            slot, head = pending.pop(pid)
            rest = head + resumed.group(1)
        call = re.match(r"^(\w+)\((.*)\)\s+=\s+(-?\d+|\?)(?:\s.*)?$", rest)
        if not call:
            raise Reject("unparsed strace call %r" % line)
        name = call.group(1)
        if name.endswith("32"):
            name = name[:-2]
        ev = (pid, name, call.group(2), None if call.group(3) == "?" else int(call.group(3)))
        if slot is None:
            events.append(ev)
        else:
            events[slot] = ev
    # Calls still unfinished when the trace ended have no result.
    return [ev for ev in events if ev is not None]


def ints(args):
    return [int(x) for x in re.findall(r"-?\d+", args)]


def setgroups_arg(args):
    m = re.match(r"^\s*(\d+),\s*(?:\[([^\]]*)\]|NULL)\s*$", args)
    if not m:
        raise Reject("unparsed setgroups arguments %r" % args)
    gids = sorted(int(g) for g in (m.group(2) or "").split(",") if g.strip())
    if len(gids) != int(m.group(1)):
        raise Reject("setgroups list %r is abbreviated" % args)
    return gids


def execve_args(args):
    path = re.match(r'^"((?:[^"\\]|\\.)*)"', args)
    argv = re.search(r"\[([^\]]*)\]", args)
    if not path or not argv or "..." in argv.group(1):
        raise Reject("unparsed execve arguments %r" % args)
    return path.group(1), re.findall(r'"((?:[^"\\]|\\.)*)"', argv.group(1))


def apply_setid(creds, name, args):
    """Linux semantics of a successful set*id call (kernel.qnt; privileged iff euid 0)."""
    c = dict(creds)
    if name == "setgroups":
        c["groups"] = setgroups_arg(args)
        return c
    kind = "uid" if name.endswith("uid") else "gid"
    r, e, s = "r" + kind, "e" + kind, "s" + kind
    if name in ("setuid", "setgid"):
        (x,) = ints(args)
        if c["euid"] is None:
            raise Reject("%s with an unknown effective uid" % name)
        if c["euid"] == 0:
            c[r] = c[e] = c[s] = x
        else:
            c[e] = x
    elif name in ("setresuid", "setresgid"):
        for key, x in zip((r, e, s), ints(args)):
            if x != -1:
                c[key] = x
    else:  # setreuid, setregid
        x_r, x_e = ints(args)
        old_r = c[r]
        if x_r != -1:
            c[r] = x_r
        if x_e != -1:
            c[e] = x_e
        if x_r != -1 or (x_e != -1 and x_e != old_r):
            c[s] = c[e]
    return c


def analyse_strace(text, sudo_bin, sudo_argv, launcher_creds):
    """Process tree, credentials and executions of one traced run.

    The credentials of the first process are unknown until the launcher (setpriv) sets all of
    them; at the exec of sudo they must equal the launcher control. From there every successful
    set*id call is applied per process (forks inherit), so the credentials of each process are
    known at every point of the trace."""
    events = parse_strace(text)
    if not events:
        raise Reject("empty strace log")
    root = events[0][0]
    creds = {root: dict.fromkeys(CRED_FIELDS)}
    birth = {}
    calls = {}
    execs = []
    start = None
    for pid, name, args, ret in events:
        if pid not in creds:
            raise Reject("process %d appears without a traced fork" % pid)
        if name in FORKS:
            if ret is not None and ret > 0:
                creds[ret] = dict(creds[pid])
                birth[ret] = dict(creds[pid])
                calls[ret] = []
            continue
        if name == "execve":
            if ret != 0:
                continue
            path, argv = execve_args(args)
            if start is None:
                if pid != root:
                    raise Reject("process %d executed %s before sudo started" % (pid, path))
                if path == sudo_bin:
                    if creds[pid] != launcher_creds:
                        raise Reject("credentials at the exec of sudo %s differ from the launcher "
                                     "control %s" % (creds[pid], launcher_creds))
                    if argv[1:] != sudo_argv:
                        raise Reject("sudo ran with arguments %s, the scenario declares %s"
                                     % (argv[1:], sudo_argv))
                    start = dict(creds[pid])
                    calls[pid] = []
                elif os.path.basename(path) != "setpriv":
                    raise Reject("the launcher executed %s" % path)
                continue
            execs.append({"pid": pid, "path": path, "argv": argv, "creds": dict(creds[pid])})
            continue
        if name not in SETID:
            raise Reject("unexpected traced call %s" % name)
        if ret != 0:
            raise Reject("%s(%s) failed in process %d" % (name, args, pid))
        creds[pid] = apply_setid(creds[pid], name, args)
        if start is not None:
            calls[pid].append({"call": name, "args": args})
    if start is None:
        raise Reject("sudo was never executed")
    return {"start": start, "creds": creds, "birth": birth, "calls": calls, "execs": execs}


# ---- derivation -----------------------------------------------------------------------------


def parse_sudo_argv(argv):
    i, runas, noninteractive = 0, None, False
    while i < len(argv) and argv[i].startswith("-"):
        if argv[i] == "-n":
            noninteractive = True
            i += 1
        elif argv[i] == "-u" and i + 1 < len(argv):
            runas = argv[i + 1]
            i += 2
        else:
            raise Reject("option %s is outside the replay grammar (-n, -u NAME)" % argv[i])
    if i == len(argv):
        raise Reject("no command in %s" % argv)
    if runas not in ACCOUNTS or ACCOUNTS[runas] == ACCOUNTS["root"]:
        raise Reject("scenarios must name an unprivileged fixture account with -u")
    return {"noninteractive": noninteractive, "runas": ACCOUNTS[runas], "command": argv[i:]}


def check_provenance(raw, fixture):
    if "REFUSED" in raw:
        raise Reject("the guest refused to run: " + raw["REFUSED"].strip())
    need(raw, "COMPLETE")
    notes = []
    inputs = parse_sums(need(raw, "meta/inputs.sha256"))
    for name in ("guest-run.sh", "sudoers", "pam.d-sudo", "scenarios"):
        if inputs.get(name) != sha256_text(fixture[name]):
            raise Reject("guest input %s differs from the committed fixture" % name)
    notes.append("guest inputs guest-run.sh, sudoers, pam.d-sudo, scenarios equal the committed fixture")
    if fixture["pam.d-sudo"].rstrip("\n") != stock_pam_d_sudo():
        raise Reject("fixture pam.d-sudo differs from STOCK_PAM_D_SUDO of test-framework/sudo-test")
    notes.append("fixture pam.d-sudo equals STOCK_PAM_D_SUDO of the compliance framework")
    installed = parse_sums(need(raw, "meta/installed.sha256"))
    if installed.get("/etc/sudoers-rs") != sha256_text(fixture["sudoers"]):
        raise Reject("installed /etc/sudoers-rs differs from the fixture")
    if installed.get("/etc/pam.d/sudo") != sha256_text(fixture["pam.d-sudo"]):
        raise Reject("installed /etc/pam.d/sudo differs from the fixture")
    notes.append("installed /etc/sudoers-rs and /etc/pam.d/sudo equal the fixture")
    binary = need(raw, "meta/binary.sha256").strip()
    if binary != need(raw, "bin/sudo.sha256").strip():
        raise Reject("binary hash measured in the guest differs from the copied-out binary")
    mode, uid, gid = need(raw, "meta/binary-stat").split()
    if int(mode, 8) != 0o755 or (uid, gid) != ("0", "0"):
        raise Reject("binary is not root:root 0755 without setuid/setgid bits (stat: %s %s %s)"
                     % (mode, uid, gid))
    notes.append("binary root:root 0755, no setuid/setgid bit; guest and host hashes agree")
    commit = need(raw, "meta/commit").strip()
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise Reject("recorded commit %r is not a full commit id" % commit)
    if not re.fullmatch(r"[0-9a-f]{64}", inputs.get("src.tar", "")):
        raise Reject("capture lacks the hash of src.tar")
    if need(raw, "meta/environment").strip() != ENVIRONMENT:
        raise Reject("the runs did not use the fixed environment %r" % ENVIRONMENT)
    return commit, binary, notes


def derive(raw):
    """All facts the replay uses, derived from the raw capture alone (plus the committed fixture)."""
    fixture = committed_fixture()
    commit, binary, notes = check_provenance(raw, fixture)
    users, uid_map, gid_map = parse_identity(raw)
    fuid, fgid = users[INVOKER]
    launcher = "setpriv --ruid=%d --euid=0 --rgid=%d --egid=%d --init-groups --" % (fuid, fgid, fgid)
    if need(raw, "meta/launcher").strip() != launcher:
        raise Reject("launcher %r differs from %r" % (raw["meta/launcher"].strip(), launcher))
    control = parse_status(need(raw, "launcher/status"), "launcher/status")
    start_creds = abstract_creds(control["creds"], uid_map, gid_map, "launch")
    sudo_bin = need(raw, "meta/binary-path").strip()
    declared = parse_scenarios(fixture["scenarios"])
    captured = sorted({k.split("/")[1] for k in raw if k.startswith("scenario/")})
    if captured != sorted(declared):
        raise Reject("captured scenarios %s differ from the fixture's %s" % (captured, sorted(declared)))
    scenarios = {}
    for name in sorted(declared):
        try:
            scenarios[name] = derive_scenario(raw, name, declared[name], sudo_bin, control,
                                              start_creds, uid_map, gid_map)
        except Reject as e:
            raise Reject("scenario %s: %s" % (name, e))
    return {
        "commit": commit,
        "binary_sha256": binary,
        "src_tar_sha256": parse_sums(raw["meta/inputs.sha256"])["src.tar"],
        "guest": {k: raw.get("meta/" + k, "").strip() for k in
                  ("kernel", "setpriv-version", "strace-version", "toolchain", "date")},
        "provenance_checks": notes,
        "scenarios": scenarios,
    }


def derive_scenario(raw, name, decl, sudo_bin, control, start_creds, uid_map, gid_map):
    d = "scenario/%s/" % name
    if need(raw, d + "declared").split() != [decl["verdict"], decl["model_cmd"]]:
        raise Reject("the guest's scenario declaration differs from the fixture")
    if need(raw, d + "argv").split("\n")[:-1] != decl["argv"]:
        raise Reject("the guest's argv differs from the fixture")
    argv = parse_sudo_argv(decl["argv"])
    if ticket_owners(need(raw, d + "ts-before"), uid_map, "ts-before"):
        raise Reject("a timestamp record existed before the run; the model starts without tickets")
    owners_after = ticket_owners(need(raw, d + "ts-after"), uid_map, "ts-after")
    trace = analyse_strace(need(raw, d + "strace"), sudo_bin, decl["argv"], control["creds"])
    exit_code = int(need(raw, d + "exit").strip())
    stdout, stderr = need(raw, d + "stdout"), need(raw, d + "stderr")
    unmodelled = []

    start = {
        "invoker": amap(uid_map, control["creds"]["ruid"], "invoker uid"),
        "session": 1, "mode": "run", "runasKind": "name", "runasArg": argv["runas"],
        "hasGroup": False, "groupArg": 0, "cmd": decl["model_cmd"], "file": "f1", "hostArg": "",
        "chroot": False, "askpass": False, "tzOffset": 0, "editorExtra": [], "statSession": 1,
    }
    placeholder = {k: 0 for k in CRED_FIELDS}
    placeholder["groups"] = []
    observed = {
        "start": start, "startCreds": start_creds, "verdict": decl["verdict"],
        "outcome": None, "calls": {"groups": [], "gid": 0, "uid": 0},
        "execCreds": placeholder, "execCmd": NOT_RUN, "ticketOwners": owners_after,
    }

    cmd_pid = None
    if len(trace["execs"]) > 1:
        raise Reject("%d programs executed after sudo; the model executes at most the command"
                     % len(trace["execs"]))
    if trace["execs"]:
        ex = trace["execs"][0]
        cmd_pid = ex["pid"]
        if exit_code != 0 or stderr != "":
            raise Reject("the command ran but sudo exited %d with stderr %r" % (exit_code, stderr))
        status = parse_status(stdout, "command output")
        if status["name"] != os.path.basename(ex["path"])[:15]:
            raise Reject("the command output comes from %s, not %s" % (status["name"], ex["path"]))
        if status["creds"] != ex["creds"]:
            raise Reject("credentials reported by the command %s differ from those traced at its "
                         "exec %s" % (status["creds"], ex["creds"]))
        if trace["birth"].get(cmd_pid) != trace["start"]:
            raise Reject("the command process did not start from sudo's launch credentials")
        names = [c["call"] for c in trace["calls"][cmd_pid]]
        if names != ["setgroups", "setgid", "setuid"]:
            raise Reject("credential calls of the command process %s are not the model's "
                         "set_groups, set_gid, set_uid" % names)
        if trace["start"]["euid"] != 0:
            raise Reject("setgid/setuid did not run privileged")
        groups_call, gid_call, uid_call = trace["calls"][cmd_pid]
        observed["calls"] = {
            "groups": sorted({amap(gid_map, g, "setgroups gid") for g in setgroups_arg(groups_call["args"])}),
            "gid": amap(gid_map, ints(gid_call["args"])[0], "setgid gid"),
            "uid": amap(uid_map, ints(uid_call["args"])[0], "setuid uid"),
        }
        observed["execCreds"] = abstract_creds(status["creds"], uid_map, gid_map, "command")
        # The program and its arguments identify the command; sudo-rs may set argv[0] freely.
        same = [ex["path"]] + ex["argv"][1:] == argv["command"]
        observed["execCmd"] = decl["model_cmd"] if same else "unmatched"
        observed["outcome"] = "exec"
        unmodelled.append("command: fsuid %d, fsgid %d, CapEff %s, NoNewPrivs %s"
                          % (status["fsuid"], status["fsgid"], status["CapEff"], status["NoNewPrivs"]))
    elif exit_code == 1 and stderr == REFUSAL and stdout == "":
        observed["outcome"] = "refused"
    else:
        raise Reject("neither a completed exec nor the policy refusal (exit %d, stderr %r): outside "
                     "the replay boundary" % (exit_code, stderr))

    others = sorted(p for p in trace["calls"] if p != cmd_pid)
    temporary = sum(len(trace["calls"][p]) for p in others)
    for p in others:
        if trace["creds"][p] != trace["start"]:
            raise Reject("process %d ends with credentials %s, not its launch credentials"
                         % (p, trace["creds"][p]))
    unmodelled.append("%d set*id calls in sudo's own processes (temporary switches for command "
                      "resolution), every process back at its launch credentials" % temporary)
    return {"observed": observed, "evidence": evidence(observed, argv), "unmodelled": unmodelled}


def evidence(observed, argv):
    """What each model step rests on (README.md, "Observed traces")."""
    ran = observed["outcome"] == "exec"
    rows = [
        ("start: invoker, argv", "observed", "strace: execve of sudo; launcher control status"),
        ("start: credentials", "observed", "strace: launcher set*id calls up to the exec of sudo, "
                                           "equal to the launcher control"),
        ("start: TZ, EDITOR", "observed", "environment fixed by `%s`" % ENVIRONMENT),
        ("start: session, /proc/self/stat session", "fixed", "not observable here; no ticket is "
                                                              "read or written in either scenario"),
        ("parse, load", "unobserved", "internal to sudo"),
        ("decide: verdict", "pinned", "fixture/scenarios, before the run"),
        ("decide: user, host, time of the request", "unobserved", "internal to sudo"),
        ("PAM: pam_start, account management, session, credentials",
         "unobserved" if ran else "not reached",
         "not modelled; no PAM event is synthesised" if ran
         else "sudo-rs refuses before any PAM call (code reading: pipeline.rs `run`)"),
    ]
    if ran:
        rows += [
            ("auth: no password check", "model step from the pinned verdict",
             "with -n, a password requirement would end the run with \"interactive authentication "
             "is required\"; observed: exit 0, empty stderr" if argv["noninteractive"] else
             "observed: exit 0, empty stderr"),
            ("setup: environment", "unobserved", "internal to sudo"),
            ("set_groups, set_gid, set_uid", "observed", "strace: arguments and results in the "
                                                         "command process"),
            ("exec: program and argv", "observed", "strace: execve; /proc/self/status Name"),
            ("exec: credentials", "observed", "/proc/self/status of the command, equal to the "
                                              "credentials traced at its exec"),
        ]
    else:
        rows.append(("refusal", "observed", "exit 1, refusal message, no execve after sudo, no "
                                            "lasting credential change"))
    rows += [
        ("helpers (none)", "observed", "strace: no other program executed"),
        ("tickets", "observed", "timestamp directory listed before and after the run"),
    ]
    return [{"element": e, "status": s, "source": src} for e, s, src in rows]


# ---- replay -----------------------------------------------------------------------------


def q_set(values, fmt):
    return "Set(%s)" % ", ".join(fmt(v) for v in values)


def q_creds(c):
    return ("{ ruid: %d, euid: %d, suid: %d, rgid: %d, egid: %d, sgid: %d, groups: %s }"
            % (c["ruid"], c["euid"], c["suid"], c["rgid"], c["egid"], c["sgid"],
               q_set(c["groups"], str)))


def q_bool(b):
    return "true" if b else "false"


def q_observed(o):
    s = o["start"]
    start = ("{ invoker: %d, session: %d, mode: %s, runasKind: %s, runasArg: %d, hasGroup: %s, "
             "groupArg: %d, cmd: %s, file: %s, hostArg: %s, chroot: %s, askpass: %s, tzOffset: %d, "
             "editorExtra: %s, statSession: %d }"
             % (s["invoker"], s["session"], json.dumps(s["mode"]), json.dumps(s["runasKind"]),
                s["runasArg"], q_bool(s["hasGroup"]), s["groupArg"], json.dumps(s["cmd"]),
                json.dumps(s["file"]), json.dumps(s["hostArg"]), q_bool(s["chroot"]),
                q_bool(s["askpass"]), s["tzOffset"], q_set(s["editorExtra"], json.dumps),
                s["statSession"]))
    c = o["calls"]
    return ("{\n    start: %s,\n    startCreds: %s,\n    verdict: %s,\n    outcome: %s,\n"
            "    calls: { groups: %s, gid: %d, uid: %d },\n    execCreds: %s,\n    execCmd: %s,\n"
            "    ticketOwners: %s,\n  }"
            % (start, q_creds(o["startCreds"]), json.dumps(o["verdict"]), json.dumps(o["outcome"]),
               q_set(c["groups"], str), c["gid"], c["uid"], q_creds(o["execCreds"]),
               json.dumps(o["execCmd"]), q_set(o["ticketOwners"], str)))


def quint_replay(observed, label):
    """Run the observation as a Quint test against a scratch copy of the model."""
    runner = "replayExec" if observed["outcome"] == "exec" else "replayRefused"
    module = ("// Generated by proofs/quint/observe/observe.py (scratch, not committed).\n"
              "// %s\nmodule observed {\n  import replay.* from \"./replay\"\n\n"
              "  pure val OBS: Observed = %s\n\n  run observedTest = %s(OBS)\n}\n"
              % (label, q_observed(observed), runner))
    tmp = tempfile.mkdtemp(prefix="lifecycle-replay.")
    try:
        for f in MODEL_FILES:
            shutil.copy(os.path.join(QUINT_DIR, f), tmp)
        with open(os.path.join(tmp, "observed.qnt"), "w", encoding="utf-8") as f:
            f.write(module)
        p = subprocess.run([os.environ.get("QUINT", "quint"), "test", "--main=observed",
                            "--backend=typescript", "--max-samples=1", "--match=^observedTest$",
                            "observed.qnt"], cwd=tmp, capture_output=True, text=True, timeout=900)
    finally:
        shutil.rmtree(tmp)
    out = re.sub(r"\x1b\[[0-9;]*m", "", p.stdout + p.stderr)
    return p.returncode == 0 and re.search(r"\b1 passing\b", out) is not None, out


def check_observation(obs):
    if obs.get("format") != FORMAT:
        raise Reject("format is not %s" % FORMAT)
    if obs.get("provenance", {}).get("kind") != KIND_REAL:
        raise Reject("not a recorded capture of the real binary (kind %r)"
                     % obs.get("provenance", {}).get("kind"))
    derived = json.loads(json.dumps(derive(obs["raw"])))
    if derived != obs.get("derived"):
        raise Reject("the derived section differs from what its raw capture gives")
    # Depends on the clone (the commit may be missing), so it is not part of `derived`.
    source = check_source(derived["commit"], derived["src_tar_sha256"])
    return derived, source


def load_json(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def cmd_record(capture, out_path):
    raw = {}
    for root, dirs, files in os.walk(capture):
        dirs.sort()
        for name in sorted(files):
            path = os.path.join(root, name)
            rel = os.path.relpath(path, capture)
            with open(path, "rb") as f:
                data = f.read()
            if rel == "bin/sudo":
                raw["bin/sudo.sha256"] = sha256_bytes(data) + "\n"
                continue
            try:
                raw[rel] = data.decode("utf-8")
            except UnicodeDecodeError:
                raise Reject("%s is not UTF-8 text" % rel)
    derived = derive(raw)
    print("     provenance: %s" % check_source(derived["commit"], derived["src_tar_sha256"]))
    obs = {
        "format": FORMAT,
        "provenance": {
            "kind": KIND_REAL,
            "recorder": "proofs/quint/observe/observe.py record",
            "recorder_sha256": sha256_file(os.path.abspath(__file__)),
        },
        "raw": raw,
        "derived": derived,
    }
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(obs, f, indent=1, sort_keys=True)
        f.write("\n")
    print("recorded %s: commit %s, binary %s, scenarios %s"
          % (out_path, derived["commit"], derived["binary_sha256"], ", ".join(derived["scenarios"])))
    return 0


def cmd_replay(paths):
    bad = 0
    for path in paths:
        try:
            derived, source = check_observation(load_json(path))
        except Reject as e:
            print("REJECTED %s: %s" % (path, e))
            bad += 1
            continue
        for note in derived["provenance_checks"] + [source]:
            print("     provenance: %s" % note)
        for name, sc in sorted(derived["scenarios"].items()):
            ok, out = quint_replay(sc["observed"], "%s scenario %s" % (path, name))
            if ok:
                print("ACCEPTED %s %s: %s replayed by the sudo-rs model; allInvariants hold"
                      % (path, name, sc["observed"]["outcome"]))
            else:
                print("REJECTED %s %s: the model cannot replay it" % (path, name))
                print("\n".join(out.splitlines()[-25:]))
                bad += 1
    return 1 if bad else 0


def model_controls(permitted, refused):
    """Benign mismatches the replay must reject (never written as observations)."""
    controls = []

    def variant(label, base, **changes):
        o = copy.deepcopy(base)
        for path, value in changes.items():
            target = o
            keys = path.split("__")
            for k in keys[:-1]:
                target = target[k]
            target[keys[-1]] = value
        controls.append((label, o))

    invoker = permitted["start"]["invoker"]
    as_invoker = {"ruid": invoker, "euid": invoker, "suid": invoker, "rgid": invoker,
                  "egid": invoker, "sgid": invoker, "groups": [invoker]}
    variant("command ran with the invoker's credentials", permitted, execCreds=as_invoker)
    variant("command kept the invoker's group", permitted,
            execCreds__groups=sorted(set(permitted["execCreds"]["groups"]) | {invoker}))
    variant("another command than the decided one ran", permitted, execCmd=refused["start"]["cmd"])
    variant("a timestamp record appeared without a password check", permitted,
            ticketOwners=[invoker])
    variant("fixture pins a password rule but no password check happened", permitted,
            verdict="passwd")
    variant("sudo started without setuid-root credentials", permitted,
            startCreds=dict(permitted["startCreds"], euid=invoker, suid=invoker))
    exec_of_refused = copy.deepcopy(refused)
    for k in ("calls", "execCreds"):
        exec_of_refused[k] = copy.deepcopy(permitted[k])
    exec_of_refused["outcome"] = "exec"
    exec_of_refused["execCmd"] = refused["start"]["cmd"]
    controls.append(("the denied request executed", exec_of_refused))
    variant("a request the fixture permits was refused", refused, verdict="nopasswd")
    return controls


def run_model_controls(permitted, refused, prefix):
    """Each control must fail inside the run: a disabled step (QNT513, or QNT508 "Cannot
    continue") or a false `expect` (QNT508). Any other failure (parse, type, tool) is a harness
    error, not a rejection."""
    bad = 0
    for label, o in model_controls(permitted, refused):
        ok, out = quint_replay(o, "negative control: " + label)
        if ok:
            print("FAIL %s control accepted: %s" % (prefix, label))
            bad += 1
        elif re.search(r"\[QNT(508|513)\]", out):
            reason = re.search(r"\[QNT\d+\]: (.*)", out).group(1)
            print("CONTROL %s rejected as required: %s (%s)" % (prefix, label, reason))
        else:
            print("FAIL %s control did not run: %s" % (prefix, label))
            print("\n".join(out.splitlines()[-25:]))
            bad += 1
    return bad


def raw_controls(obs):
    """Edits of a real capture the derivation must reject."""
    out = []

    def edited(label, fn):
        o = copy.deepcopy(obs)
        fn(o)
        out.append((label, o))

    def groups_line(o):
        key = "scenario/permitted/stdout"
        o["raw"][key] = re.sub(r"^Groups:.*$", "Groups:\t%d" % 0, o["raw"][key], flags=re.M)

    edited("command output edited (Groups line)", groups_line)
    edited("guest binary hash edited",
           lambda o: o["raw"].__setitem__("meta/binary.sha256", "0" * 64 + "\n"))
    edited("installed sudoers hash edited", lambda o: o["raw"].__setitem__(
        "meta/installed.sha256", re.sub(r"^[0-9a-f]{64}(  /etc/sudoers-rs)$", "0" * 64 + r"\1",
                                        o["raw"]["meta/installed.sha256"], flags=re.M)))
    edited("derived verdict edited", lambda o: o["derived"]["scenarios"]["refused"]["observed"]
           .__setitem__("verdict", "nopasswd"))
    edited("provenance kind edited",
           lambda o: o["provenance"].__setitem__("kind", "harness-expectation"))
    return out


def cmd_controls(path):
    obs = load_json(path)
    try:
        derived, _ = check_observation(obs)
    except Reject as e:
        print("REJECTED %s: %s (controls need an accepted observation)" % (path, e))
        return 1
    sc = derived["scenarios"]
    if set(sc) != {"permitted", "refused"}:
        print("FAIL controls expect the scenarios permitted and refused")
        return 1
    bad = 0
    for name in ("permitted", "refused"):
        ok, out = quint_replay(sc[name]["observed"], "%s scenario %s" % (path, name))
        if not ok:
            print("FAIL %s %s is not accepted; controls would be meaningless" % (path, name))
            print("\n".join(out.splitlines()[-25:]))
            return 1
    for label, o in raw_controls(obs):
        try:
            check_observation(o)
            print("FAIL raw control accepted: %s" % label)
            bad += 1
        except Reject as e:
            print("CONTROL raw rejected as required: %s (%s)" % (label, e))
    bad += run_model_controls(sc["permitted"]["observed"], sc["refused"]["observed"], "model")
    return 1 if bad else 0


def harness_expectation(decl):
    """What the fixture leads one to expect; checks the harness only, never an observation."""
    argv = parse_sudo_argv(decl["argv"])
    alice, target = ACCOUNTS[INVOKER], argv["runas"]
    ran = decl["verdict"] == "nopasswd"
    return {
        "start": {"invoker": alice, "session": 1, "mode": "run", "runasKind": "name",
                  "runasArg": target, "hasGroup": False, "groupArg": 0, "cmd": decl["model_cmd"],
                  "file": "f1", "hostArg": "", "chroot": False, "askpass": False, "tzOffset": 0,
                  "editorExtra": [], "statSession": 1},
        "startCreds": {"ruid": alice, "euid": 0, "suid": 0, "rgid": alice, "egid": alice,
                       "sgid": alice, "groups": [alice]},
        "verdict": decl["verdict"],
        "outcome": "exec" if ran else "refused",
        "calls": {"groups": [target], "gid": target, "uid": target} if ran
        else {"groups": [], "gid": 0, "uid": 0},
        "execCreds": {"ruid": target, "euid": target, "suid": target, "rgid": target,
                      "egid": target, "sgid": target, "groups": [target]} if ran
        else {k: ([] if k == "groups" else 0) for k in CRED_FIELDS},
        "execCmd": decl["model_cmd"] if ran else NOT_RUN,
        "ticketOwners": [],
    }


def cmd_selftest():
    print("HARNESS self-test: fixture expectations, not observations of the binary")
    declared = parse_scenarios(committed_fixture()["scenarios"])
    exp = {name: harness_expectation(d) for name, d in declared.items()}
    bad = 0
    for name in sorted(exp):
        ok, out = quint_replay(exp[name], "harness expectation " + name)
        print("%s harness expectation %s" % ("PASS" if ok else "FAIL", name))
        if not ok:
            print("\n".join(out.splitlines()[-25:]))
            bad += 1
    if bad:
        return 1
    bad += run_model_controls(exp["permitted"], exp["refused"], "harness")
    return 1 if bad else 0


def main(argv):
    if len(argv) == 3 and argv[0] == "record":
        cmd = lambda: cmd_record(argv[1], argv[2])
    elif len(argv) >= 2 and argv[0] == "replay":
        cmd = lambda: cmd_replay(argv[1:])
    elif len(argv) == 2 and argv[0] == "controls":
        cmd = lambda: cmd_controls(argv[1])
    elif argv == ["selftest"]:
        cmd = cmd_selftest
    else:
        print(__doc__, file=sys.stderr)
        return 2
    try:
        return cmd()
    except Reject as e:
        print("REJECTED: %s" % e)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
