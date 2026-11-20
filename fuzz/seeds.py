#!/usr/bin/env python3
"""Write the seed corpora of the fuzz targets, taken from the unit-test inputs of sudo-rs.

    python3 fuzz/seeds.py <output directory>      (from the repository root)

Creates <output directory>/<target>/<sha1 of the seed> for every target of fuzz/Cargo.toml.
Sources: string literals of the sudoers, defaults and command tests, the request triples of
`permission_test`, the argument vectors of the sudo and su CLI tests, docs/sudoers.example, and
hand-written inputs where a component has no tests (visudo's command line, timestamp records,
which are encoded here exactly as `SessionRecord::encode` writes them).
"""

import hashlib
import os
import re
import struct
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LITERAL = re.compile(r'r(#*)"(.*?)"\1|"((?:[^"\\]|\\.)*)"', re.S)
ESCAPES = {"n": "\n", "t": "\t", "r": "\r", "0": "\0", "\\": "\\", '"': '"', "'": "'"}


def read(path):
    with open(os.path.join(ROOT, path), encoding="utf-8") as f:
        return f.read()


def unescape(body):
    out, i = [], 0
    while i < len(body):
        c = body[i]
        if c != "\\":
            out.append(c)
            i += 1
            continue
        n = body[i + 1]
        if n in ESCAPES:
            out.append(ESCAPES[n])
            i += 2
        elif n == "x":
            out.append(chr(int(body[i + 2 : i + 4], 16)))
            i += 4
        elif n == "u":
            end = body.index("}", i)
            out.append(chr(int(body[i + 3 : end], 16)))
            i = end + 1
        elif n == "\n":  # line continuation: skip the newline and leading whitespace
            i += 2
            while i < len(body) and body[i] in " \t":
                i += 1
        else:
            out.append(n)
            i += 2
    return "".join(out)


def literals(text):
    for m in LITERAL.finditer(text):
        yield m.group(2) if m.group(2) is not None else unescape(m.group(3))


def tests_of(path):
    """The part of a source file after its first `#[cfg(test)]` (or all of a test file)."""
    text = read(path)
    if path.endswith(("test/mod.rs", "tests.rs")):
        return text
    i = text.find("#[cfg(test)]")
    return text[i:] if i >= 0 else ""


seeds = {}


def add(target, data):
    if isinstance(data, str):
        data = data.encode()
    seeds.setdefault(target, set()).add(data)


# ---------------------------------------------------------------- sudoers text

SUDOERS_SOURCES = [
    "src/sudoers/test/mod.rs",
    "src/sudoers/ast.rs",
    "src/sudoers/basic_parser.rs",
    "src/sudoers/tokens.rs",
    "src/sudoers/policy.rs",
    "src/defaults/mod.rs",
]
policy_lines = set()
for path in SUDOERS_SOURCES:
    text = tests_of(path)
    for lit in literals(text):
        if len(lit) >= 2:
            policy_lines.add(lit)
    # groups of lines given together: sudoer![..], pass!([..]), FAIL!([..])
    for m in re.finditer(r'(?:sudoer!\s*\[|(?:pass|FAIL|SYNTAX)!\s*\(\s*\[)(.*?)\]', text, re.S):
        group = list(literals(m.group(1)))
        if group:
            policy_lines.add("\n".join(group) + "\n")

example = read("docs/sudoers.example")
policy_lines.add(example)
for line in policy_lines:
    add("sudoers_parse", line if line.endswith("\n") else line + "\n")

# ---------------------------------------------------------------- decisions

REQUEST = re.compile(
    r'(?:pass|FAIL)!\s*\(\s*\[(?P<policy>.*?)\]\s*,\s*"(?P<am>[^"]*)"\s*=>\s*'
    r'(?:root\(\)|request!\s*\{\s*(?P<tu>\w+)\s*(?:,\s*(?P<tg>\w+)\s*)?\})\s*,\s*'
    r'"(?P<host>[^"]*)"\s*;\s*"(?P<cmd>[^"]*)"',
    re.S,
)
test_text = read("src/sudoers/test/mod.rs")
for m in REQUEST.finditer(test_text):
    tu = m.group("tu") or "root"
    tg = m.group("tg") or tu
    policy = "\n".join(literals(m.group("policy")))
    header = f"{m.group('am')}:{tu}:{tg}:{m.group('host')}\n{unescape(m.group('cmd'))}\n"
    add("sudoers_decide", header + policy + "\n")
for line in sorted(policy_lines):
    add("sudoers_decide", "user:root:root:server\n/bin/ls -l\n" + line)

# ---------------------------------------------------------------- Defaults

defaults_block = read("src/defaults/mod.rs").split("defaults! {", 1)[1].split("\n}", 1)[0]
names = re.findall(r"^\s+(\w+)\s+=", defaults_block, re.M)
HEADER = "user:root:root:server\n/bin/ls -l\n"
for name in names:
    for form in (f"Defaults {name}", f"Defaults !{name}", f"Defaults {name}=1",
                 f'Defaults {name}="x"', f"Defaults {name}+=FOO", f"Defaults {name}-=PATH"):
        add("sudoers_defaults", HEADER + form + "\n")
for scope in ("Defaults@server", "Defaults:user", "Defaults>root", "Defaults!/bin/ls",
              "Defaults:%users", "Defaults@laptop"):
    for setting in ("env_keep+=FOO", "!use_pty", "secure_path=/usr/bin:/bin", "noexec",
                    "timestamp_timeout=2.5", "umask=0077", "passwd_tries=1000", "rootpw",
                    'editor="/usr/bin/vi:/usr/bin/nano"', "env_editor", "!env_editor"):
        add("sudoers_defaults", HEADER + f"{scope} {setting}\n")
for line in policy_lines:
    if "Defaults" in line:
        add("sudoers_defaults", HEADER + (line if line.endswith("\n") else line + "\n"))
add("sudoers_defaults", HEADER + example)

# ---------------------------------------------------------------- command lines

ARRAY = re.compile(r'\[\s*((?:r?#*"(?:[^"\\]|\\.)*"#*\s*,\s*)*r?#*"(?:[^"\\]|\\.)*"#*)\s*,?\s*\]')
for m in ARRAY.finditer(tests_of("src/sudo/cli/tests.rs")):
    args = list(literals(m.group(1)))
    if not args[0].startswith(("sudo", "/usr/bin/sudo", "/bin/sudo")):
        args.insert(0, "sudo")
    add("sudo_cli", "\0".join(args))
for argv0 in ("sudo", "sudoedit", "/usr/bin/sudoedit-rs"):
    for rest in ([], ["-l"], ["-ll", "-U", "alice"], ["-e", "/etc/hosts"], ["-s"], ["-i", "id"],
                 ["-u", "#1000", "-g", "#10", "--", "ls", "-l"], ["--preserve-env=PATH,HOME", "env"],
                 ["FOO=bar", "env"], ["-D", "/tmp", "pwd"], ["-v"], ["-k"], ["-K"], ["-V"], ["-h"],
                 ["sudoedit", "file"], ["--user=root", "--chdir=/", "-AbBnS", "-pX", "cmd"]):
        add("sudo_cli", "\0".join([argv0] + rest))

for m in ARRAY.finditer(tests_of("src/su/cli.rs")):
    add("su_cli", "\0".join(["/bin/su"] + list(literals(m.group(1)))))

for rest in ([], ["-c"], ["--check"], ["-f", "/etc/sudoers"], ["--file=/etc/sudoers.d/x"],
             ["-o", "-p"], ["--owner", "--perms", "-c", "-f", "x"], ["-h"], ["--help"], ["-V"],
             ["--version"], ["-q"], ["-s", "-x", "-"], ["/etc/sudoers"], ["-cf/etc/sudoers"],
             ["--", "-c"]):
    add("visudo_cli", "\0".join(["visudo"] + rest))

# ---------------------------------------------------------------- timestamp records


def record(tty, pid, session, start, auth_uid, timestamp, enabled):
    # RecordScope::encode, SessionRecord::encode (little-endian x86-64 layout)
    if tty:
        scope = struct.pack("<BQi", 1, pid, session)
    else:
        scope = struct.pack("<Bii", 2, pid, session)
    scope += struct.pack("<qq", *start)
    return scope + struct.pack("<I", auth_uid) + struct.pack("<qq", *timestamp) + bytes(
        [0xFF if enabled else 0x00]
    )


RECORDS = [
    record(True, 0x8801, 100, (1000, 5), 1000, (50, 0), True),
    record(True, 0x8801, 100, (1000, 5), 0, (50, 0), False),
    record(False, 200, 100, (2000, 0), 1000, (60, 999_999_999), True),
    record(True, 0x8802, 300, (3000, 999_999_999), 1000, (1, 1), True),
]
HEADER_TS = struct.pack("<HH", 0x50D0, 2)
for r in RECORDS:
    add("timestamp", b"\x00" + r)
for ops in (b"", b"\x01", b"\x00\x01", b"\x05\x06\x00", b"\x09\x0a\x08", b"\x0d\x0e\x0c\x01",
            b"\x02\x00\x01\x04\x05\x06\x08\x09"):
    for body in (b"", HEADER_TS, HEADER_TS + b"".join(struct.pack("<H", len(r)) + r for r in RECORDS),
                 HEADER_TS + struct.pack("<H", len(RECORDS[0])) + RECORDS[0][:-3],
                 HEADER_TS + struct.pack("<H", 0), struct.pack("<HH", 0x50D0, 1)):
        add("timestamp", bytes([1, len(ops)]) + ops + body)

# ---------------------------------------------------------------- names and escaping

for name in ("root", "user", "#0", "#1000", "#4294967295", "#-1", "#+5", "#", "", "#1x",
             "ferris", "user name", "#0123"):
    add("name_escape", b"\x00" + name.encode())
for m in ARRAY.finditer(tests_of("src/common/command.rs")):
    add("name_escape", b"\x01" + "\0".join(literals(m.group(1))).encode())
for args in (["a"], [""], ["", ""], ["a b", "c\\d"], ["$HOME", "`id`", "'q'", '"q"'], ["\n"],
             ["-c", "x;y"]):
    add("name_escape", b"\x01" + "\0".join(args).encode())
add("name_escape", b"\x01\xff\x00\xc3")

# ---------------------------------------------------------------- dictionary of the sudoers targets

KEYWORDS = [
    "ALL", "Defaults", "User_Alias", "Runas_Alias", "Host_Alias", "Cmnd_Alias", "Cmd_Alias",
    "@include", "@includedir", "#include", "#includedir", "sudoedit", "list", "NOPASSWD:",
    "PASSWD:", "NOEXEC:", "EXEC:", "SETENV:", "NOSETENV:", "MAIL:", "NOMAIL:", "FOLLOW:",
    "NOFOLLOW:", "INTERCEPT:", "NOINTERCEPT:", "LOG_INPUT:", "LOG_OUTPUT:", "CWD=", "CHROOT=",
    "APPARMOR_PROFILE=", "ROLE=", "TYPE=", "TIMEOUT=", "NOTBEFORE=", "NOTAFTER=", "sha224:",
    "sha256:", "(ALL)", "(ALL:ALL)", "(:", "%", "%:", "#", "!", "\\\n", '"', "+=", "-=", "=",
    "^", "$", "*", "?", "[!", "]", "/usr/bin/", "Defaults@", "Defaults:", "Defaults>", "Defaults!",
]


def dict_entry(word):
    escaped = "".join(c if 32 <= ord(c) < 127 and c not in '"\\' else f"\\x{ord(c):02x}" for c in word)
    return f'"{escaped}"\n'


out = sys.argv[1]
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "sudoers.dict"), "w") as f:
    for word in KEYWORDS + names:
        f.write(dict_entry(word))

# ---------------------------------------------------------------- write

for target, items in sorted(seeds.items()):
    d = os.path.join(out, target)
    os.makedirs(d, exist_ok=True)
    for data in items:
        with open(os.path.join(d, hashlib.sha1(data).hexdigest()), "wb") as f:
            f.write(data)
    print(f"{target}: {len(items)} seeds")
