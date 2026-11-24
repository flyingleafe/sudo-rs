#!/usr/bin/env python3
"""Compare sudo-rs (the parser dump) with C sudo 1.9.18 on the parser corpus and classify
every difference. proofs/parser/C-SUDO.md describes the method and the categories.

usage: parser_compare.py CORPUS RUST_DUMP C_OUT [DETAILS]

  CORPUS     `parser corpus` output (`<label> <quoted text>` per line)
  RUST_DUMP  `dump_corpus` output (`parser-dump 2` header, then `case <label>` + dump records)
  C_OUT      `parser csudo` output
  DETAILS    optional output: one line per difference (label, line, category, messages)

Prints the summary (markdown tables) on stdout. Python 3, standard library only.

Method, per case:
1. sudo-rs: the dump records are grouped into the iterations of `parse_lines`; each gets the
   physical line it starts on (reconstruction checked against the records).
2. C sudo: the diagnostics of `visudo -c` with their line and column.
3. Both are mapped to logical lines (physical lines joined by a final backslash). A logical line
   is kept by C if C reports no error on it; an iteration of sudo-rs is kept if it is an accepted
   item.
4. Every logical line on which the two differ is one difference, classified by the first
   matching rule (rule tables below, in order). A difference no rule matches is "unclassified".
5. Where both accept the whole file, the entries are compared with `cvtsudoers -f json`.
"""

import collections
import json
import os
import re
import sys

from parser_lean_compare import check_dump_header

FIXTURE = "/tmp/sudo-rs-parser-dump-fixture"

# --------------------------------------------------------------------------- reading


def unquote(s):
    """Decode one quoted string (DUMP.md) at the start of s; return (text, rest)."""
    assert s[0] == '"', s[:20]
    out = []
    i = 1
    while True:
        c = s[i]
        if c == '"':
            return "".join(out), s[i + 1:]
        if c == "\\":
            n = s[i + 1]
            if n in '"\\':
                out.append(n)
                i += 2
            else:
                j = s.index("}", i)
                out.append(chr(int(s[i + 3:j], 16)))
                i = j + 1
        else:
            out.append(c)
            i += 1


def read_corpus(path):
    cases = []
    with open(path, encoding="ascii") as f:
        for line in f:
            label, rest = line.rstrip("\n").split(" ", 1)
            cases.append((label, unquote(rest)[0]))
    return cases


def read_dump(path):
    out = {}
    cur = None
    with open(path, encoding="ascii") as f:
        check_dump_header(f)
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("case "):
                cur = line[5:]
                out[cur] = []
            else:
                out[cur].append(line)
    if not out:
        raise SystemExit(f"{path}: no cases")
    return out


def read_hostdep(path):
    """Labels of the cases whose command patterns name existing host paths (the harness writes
    them next to the dump). Such a case can be canonicalized here and not there, or the other
    way round: a difference in it is a limit of comparing across hosts, not a parser cause."""
    try:
        with open(path, encoding="ascii") as f:
            return {line.split(" ")[0] for line in f if line.strip()}
    except FileNotFoundError:
        return set()


def read_c(path):
    out = {}
    cur = None
    with open(path, encoding="ascii") as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("case "):
                cur = line[5:]
                out[cur] = {}
            elif line.startswith("visudo "):
                _, st, rest = line.split(" ", 2)
                out[cur]["visudo"] = (int(st), unquote(rest)[0])
            elif line.startswith("testsudoers "):
                _, st, rest = line.split(" ", 2)
                o, rest = unquote(rest)
                e, _ = unquote(rest.lstrip())
                out[cur]["ts"] = (int(st), o, e)
            elif line == "cvtsudoers skipped":
                out[cur]["cvt"] = None
            elif line.startswith("cvtsudoers "):
                _, st, rest = line.split(" ", 2)
                out[cur]["cvt"] = (int(st), unquote(rest)[0])
    return out


# --------------------------------------------------------------------------- dump terms


def sexp(s):
    """Parse one dump term: atoms, ("str", text), (tuples) and [lists]."""
    pos = 0
    atom = re.compile(r"[^ ()\[\]]+")

    def term():
        nonlocal pos
        c = s[pos]
        if c in "([":
            close = ")" if c == "(" else "]"
            pos += 1
            items = []
            while s[pos] != close:
                if s[pos] == " ":
                    pos += 1
                    continue
                items.append(term())
            pos += 1
            return tuple(items) if close == ")" else list(items)
        if c == '"':
            text, rest = unquote(s[pos:])
            pos = len(s) - len(rest)
            return ("str", text)
        m = atom.match(s, pos)
        pos = m.end()
        return m.group(0)

    return term()


def S(x):
    return x[1] if isinstance(x, tuple) and x and x[0] == "str" else x


# --------------------------------------------------------------------------- lines


def is_continued(line, strict=False):
    """C sudo reads a physical line as continued on the next when it ends in a backslash, then
    optional blanks, outside a comment (an even number of backslashes is an escaped one).
    strict: sudo-rs, where only a backslash immediately before the newline continues."""
    if not strict:
        line = line.rstrip(" \t")
    if not line.endswith("\\"):
        return False
    stripped = line.lstrip(" \t")
    if stripped.startswith("#") and not re.match(r"#(include|includedir)\b|#\d", stripped):
        return False
    if re.search(r"(^|[ \t])#(?![0-9]|include)", line):
        return False
    return (len(line) - len(line.rstrip("\\"))) % 2 == 1


def logical_lines(text):
    """(map physical line -> first physical line of its logical line, physical lines)."""
    lines = text.split("\n")
    start = {}
    cur = None
    for i, l in enumerate(lines, 1):
        if cur is None:
            cur = i
        start[i] = cur
        if not is_continued(l):
            cur = None
    return start, lines


def logical_text(lines, start, first):
    return "\n".join(l for n, l in enumerate(lines, 1) if start.get(n) == first)


# --------------------------------------------------------------------------- sudo-rs iterations

FATAL = re.compile(r"fatal (\d+):(\d+)-(\d+):(\d+) (\".*\")$")


def rs_iterations(records, text):
    """Group the records into iterations of parse_lines, each with its start line.

    An iteration: an item (ok or fatal) followed, for an accepted item, by an optional "garbage
    at end of line" or "missing line terminator" fatal. After a fatal, parse_lines consumes a
    comment or a newline at the stopping point, or else skips the rest of the physical line and
    the next iteration reads the newline as an (artifact) comment. Returns (iterations,
    consistent)."""
    start, lines = logical_lines(text)
    nlines = len(lines)
    its = []
    cur = 1
    i = 0
    consistent = True

    def after_stop(el, ec):
        """Next start line after the stream stopped at (el, ec); may consume an artifact.

        parse_lines consumes a comment at the stopping point (`#`) or a newline there, and
        otherwise skips to the end of the physical line, whose newline the next iteration then
        reads as a comment. A reported position can lie before the actual stopping point (an
        error created with the position of the construct), so an artifact comment is required
        only when the position itself holds a `#` that no record explains."""
        nonlocal i, consistent
        line = lines[el - 1] if el - 1 < nlines else ""
        ch = line[ec - 1] if ec - 1 < len(line) else ("\n" if el < nlines else None)
        if ch in ("#", "\n") or ch is None or el >= nlines:
            return el + 1
        if i < len(records) and records[i] == "ok comment":
            its.append({"line": el, "kind": "comment", "garbage": None, "artifact": True})
            i += 1
        return el + 1

    while i < len(records):
        r = records[i]
        it = {"line": cur, "garbage": None}
        if r.startswith("panic "):
            it.update(kind="panic", msg=unquote(r[6:])[0])
            its.append(it)
            break
        if r.startswith("fatal "):
            m = FATAL.match(r)
            span = tuple(int(m.group(k)) for k in range(1, 5))
            it.update(kind="error", msg=unquote(m.group(5))[0], span=span)
            cur = span[0]  # the error names the line of the construct
            its.append(it)
            if span[2] < cur:
                consistent = False
            i += 1
            cur = after_stop(span[2], span[3])
            continue
        if not r.startswith("ok "):
            consistent = False
            i += 1
            continue
        item = r[3:]
        it.update(kind="comment" if item == "comment" else "item", item=item)
        its.append(it)
        i += 1
        if i < len(records) and records[i].startswith("fatal ") and (
                '"garbage at end of line"' in records[i]
                or '"missing line terminator at end of file"' in records[i]):
            m = FATAL.match(records[i])
            span = tuple(int(m.group(k)) for k in range(1, 5))
            it["garbage"] = (span, unquote(m.group(5))[0])
            i += 1
            if span[0] < nlines and i < len(records) and records[i] == "ok comment":
                its.append({"line": span[0], "kind": "comment", "garbage": None, "artifact": True})
                i += 1
            cur = span[0] + 1
            continue
        if it["kind"] == "comment":
            cur += 1
        elif i < len(records) and records[i].startswith("fatal "):
            # a following error gives its own position: a comment inside the item can end it
            # before the logical line does
            m = FATAL.match(records[i])
            cur = max(cur, int(m.group(1)))
        else:
            last = cur
            while last < nlines and is_continued(lines[last - 1], strict=True):
                last += 1
            cur = last + 1
            # a comment inside the item can end it earlier than its logical line: the next
            # error record starts no later than the line it names
            for later in records[i:]:
                if later.startswith("fatal "):
                    cur = min(cur, int(FATAL.match(later).group(1)))
                    break
    return its, consistent


# --------------------------------------------------------------------------- C diagnostics

CMSG = re.compile(r"^(?:Error: |Warning: )?sudoers:(\d+):(\d+): (.*)$")


def c_messages(case, text):
    """C diagnostics of visudo -c: list of (line or None, column or None, message, severity)."""
    out = []
    seen = set()
    for l in case["visudo"][1].split("\n"):
        m = CMSG.match(l)
        if m:
            sev = "warning" if l.startswith("Warning:") else "error"
            key = (int(m.group(1)), m.group(3))
            if key not in seen:
                seen.add(key)
                out.append((int(m.group(1)), int(m.group(2)), m.group(3), sev))
        elif l.startswith("visudo: "):
            msg = l[len("visudo: "):]
            line = None
            mm = re.match(r"(.*): No such file or directory$", msg)
            if mm:
                p = mm.group(1)
                for n, tl in enumerate(text.split("\n"), 1):
                    if "include" in tl and (p in tl or p.split("/")[-1] in tl):
                        line = n
                        break
            out.append((line, None, msg, "error"))
    return out


def msg_shape(msg):
    """A message with its variable parts replaced: names in double quotes and numbers."""
    shape = re.sub(r'"[^"]*"', '"…"', msg)
    return re.sub(r"\b\d+\b", "N", shape)


def advisory_shapes(cases):
    """The message shapes that occur when `visudo -c` accepted the file: an advisory is not a
    rejection. Derived from the data of the run, so that a new shape shows up in the report."""
    shapes = collections.Counter()
    for c in cases:
        if c["visudo"][0] != 0:
            continue
        for _, _, msg, sev in c_messages(c, ""):
            if sev == "error":
                shapes[msg_shape(msg)] += 1
    return shapes


# --------------------------------------------------------------------------- classification

def char_class(c):
    if c is None or c == "":
        return "end of line"
    if c == "\r":
        return "carriage return"
    o = ord(c)
    if o > 127:
        return "non-ASCII character"
    if o < 32 or o == 127:
        return "control character"
    return None


# sudo-rs error message -> category
RS_RULES = [
    (r"is not supported by sudo-rs", lambda m: "unsupported by sudo-rs: " + m.split(" ")[0] + " option"),
    (r"SELinux role based access control", "unsupported by sudo-rs: ROLE/TYPE option"),
    (r"netgroups are not supported", "unsupported by sudo-rs: netgroup"),
    (r"digest specifications are not supported", "unsupported by sudo-rs: command digest"),
    (r"regular expressions are not supported", "unsupported by sudo-rs: regular expression"),
    (r"unsupported modifier", "unsupported by sudo-rs: other NAME= option"),
    (r"^unknown setting", "Defaults: setting unknown to sudo-rs"),
    (r"is not a valid value for|can't assign to boolean|is not a boolean setting|cannot be used in a boolean context|is not a list parameter|double quotes are required|empty string not allowed",
     "Defaults: value or kind check stricter in sudo-rs"),
    (r"hosts cannot be specified using an IPv4 address", "host: IPv4 address rejected by sudo-rs"),
    (r"token exceeds maximum length", "limit: token length (sudo-rs MAX_LEN)"),
    (r"too many items in list|too many tags|environment variable list too long", "limit: list length (sudo-rs 127)"),
    (r"value too large", "limit: numeric id does not fit u32"),
    (r"glob patterns are not allowed in command arguments", "command: wildcard in arguments rejected by sudo-rs"),
    (r"list does not take arguments", "command: 'list' with arguments rejected by sudo-rs"),
    (r"wildcard pattern error", "command: glob syntax rejected by sudo-rs"),
    (r"fully qualified path needed", "command: path form rejected by sudo-rs"),
    (r"path cannot contain", "option: CWD path rejected by sudo-rs"),
    (r"use quotes around filenames|unknown directive", "include: path or directive syntax"),
    (r"illegal escape sequence", "escape: sequence rejected by sudo-rs"),
    (r"stray escape sequence", "continuation: backslash after whitespace not followed by newline"),
    (r"missing line terminator", "end of file: last line without newline"),
    (r"reserved word", "alias: reserved name rejected by sudo-rs"),
    (r"embedded \$ in username", "token class: '$' inside a user name"),
    (r"ambiguous syntax", "directive: keyword in a user list"),
]

# sudo-rs syntax errors: (text before the error start, text from it) -> category
RS_CONTEXT_RULES = [
    (r"\+$", r"", "unsupported by sudo-rs: netgroup"),
    (r"^Defaults!!+\s*!*\s*$", r"", "Defaults! scope: a second '!' with no item after it"),
    (r"#$", r"^-", "user id: '#-N' rejected by sudo-rs"),
    (r"", r"^#-", "user id: '#-N' rejected by sudo-rs"),
    (r"\\$", r"^[^\n]", "escape: sequence rejected by sudo-rs"),
    (r"\"[^\"]*\\\"?$", r"", "quoted user: escaped '\"' inside quotes rejected by sudo-rs"),
    (r"=\s*\"[^\"]*$", r"", "Defaults: quoted list item rejected by sudo-rs"),
    (r"[A-Z_]+\s*=\s*$", r"^\"", "option: quoted value rejected by sudo-rs"),
    (r"^\s*Defaults.*=\s*[0-9a-fA-F.]*$", r"", "Defaults: value syntax rejected by sudo-rs"),
    (r"(^|[\s,(!:])\"[^\"=]*$", r"^[^\"]*\"", "F-P3: quoted user whose content is not a user name"),
    (r"", r"^\"[^\"]*\"", "F-P3: quoted user whose content is not a user name"),
    (r"", r"^[\w.-]*\*", "host: wildcard host name rejected by sudo-rs"),
    (r"", r"^[0-9a-fA-F]*::?[0-9a-fA-F:]", "host: IPv6 address rejected by sudo-rs"),
    (r"", r"^[0-9.]+/", "host: network/mask rejected by sudo-rs"),
    (r"[0-9.]$", r"^/\d", "host: network/mask rejected by sudo-rs"),
    (r"", r"^\^", "unsupported by sudo-rs: regular expression"),
]


def line_rule(logical):
    """Rules on the whole logical line."""
    if logical.count(",") >= 127 or logical.count(":") >= 127 or \
            len(re.findall(r"\b[A-Z]\d+\b", logical)) >= 127:
        return "limit: list length (sudo-rs 127)"
    if "\\\n" in logical:
        return "continuation: inside a token (C joins or splits differently)"
    return None


def classify_rs(msg, text, span, logical, item_line):
    """A line where sudo-rs reports msg (empty for 'garbage') at span and C reports nothing;
    item_line: the line the sudo-rs item started on."""
    lines = text.split("\n")
    sl, sc, el, ec = span
    sline = lines[sl - 1] if sl - 1 < len(lines) else ""
    before, at = sline[:sc - 1], sline[sc - 1:]
    generic = msg == "" or msg.startswith(("expected ", "expecting ", "garbage at end of line"))
    if generic:
        consumed = "\n".join(lines[item_line - 1:el - 1] + [lines[el - 1][:ec - 1] if el - 1 < len(lines) else ""])
        cat = line_rule(logical)
        if not cat and "\\\n" in consumed:
            cat = "continuation: inside a token (C joins or splits differently)"
        if cat:
            return cat
        for b, a, cat in RS_CONTEXT_RULES:
            if re.search(b, before) and re.search(a, at):
                return cat
    if msg.startswith("expecting '"):
        if '"' in msg:
            return "quoting: sudo-rs requires the closing quote before the next token"
        if ')' in msg:
            return "runas: an error inside the user list is discarded and the list ends early (F-P3)"
    for pat, cat in RS_RULES:
        if re.search(pat, msg):
            return cat(msg) if callable(cat) else cat
    line = lines[el - 1] if el - 1 < len(lines) else ""
    ch = line[ec - 1] if 0 <= ec - 1 < len(line) else None
    cc = char_class(ch)
    if cc:
        return "token class: " + cc + " (sudo-rs stops)"
    if generic and not ch.isalnum():
        return f"token class: sudo-rs stops at '{ch}' where C continues"
    return None


# C error message -> category
C_RULES = [
    (r"duplicate (User|Runas|Host|Cmnd)_Alias|referenced but not defined|cycle in",
     "alias: checked by C at parse time (sudo-rs: in analysis)"),
    (r"^values for|no value specified|^empty string|value .* is invalid|invalid value|out of range|must be|is deprecated|invalid \w+ value",
     "Defaults or option: value check stricter in C"),
    (r"No such file or directory|unable to open|unable to read|Not a directory|is not a regular file$",
     "include: target does not exist or has the wrong type"),
    (r"expected a fully-qualified path name", "path check stricter in C"),
    (r"invalid sudoedit file name", "command: sudoedit argument check in C"),
    (r"unknown defaults entry", "Defaults: setting unknown to C"),
    (r"empty group", "user: '%' without a group name"),
    (r"^empty netgroup$", "user: empty netgroup rejected by C"),
    (r"^: ", "include: empty path after the directive (C reports the open failure)"),
    (r"is (world|group) writable$|not owned by|is not owned|wrong owner|wrong mode",
     "include: C checks the include target's owner and mode, sudo-rs leaves it to the open"),
    (r"unexpected line break in string|invalid line continuation", "continuation: inside a quoted string (C)"),
]

KEYWORDS = r"(ROLE|TYPE|CWD|CHROOT|TIMEOUT|NOTBEFORE|NOTAFTER|INTERCEPT|NOINTERCEPT|APPARMOR_PROFILE|sudoedit|list)"
TAGS = r"(PASSWD|NOPASSWD|SETENV|NOSETENV|EXEC|NOEXEC|LOG_INPUT|NOLOG_INPUT|LOG_OUTPUT|NOLOG_OUTPUT|MAIL|NOMAIL|FOLLOW|NOFOLLOW|INTERCEPT|NOINTERCEPT)"

# C syntax errors: (text before C's error column, text from it) -> category
C_CONTEXT_RULES = [
    (r"!\s+$", r"^!", "negation: '!' separated by whitespace rejected by C"),
    (r"", r"^!+[ \t]", "negation: '!' followed by whitespace in a Defaults binding rejected by C"),
    (r"^\s*Defaults\S*.*!\s+$", r"", "negation: '!' followed by whitespace in a Defaults binding rejected by C"),
    (r"^\s*Defaults$", r"^[@:>!][^ \t]*![ \t]", "negation: '!' followed by whitespace in a Defaults binding rejected by C"),
    (r"^\s*Defaults[@:>!].*![ \t]", r"", "negation: '!' followed by whitespace in a Defaults binding rejected by C"),
    (r"\b" + TAGS + r"\s*:\s*$", r"^(CWD|CHROOT|APPARMOR_PROFILE|ROLE|TYPE|TIMEOUT|NOTBEFORE|NOTAFTER)\s*=",
     "option after tag rejected by C"),
    (r"(^|[\s,!(:=])$", r"^" + KEYWORDS + r"\b", "keyword as a name: reserved by C, a name or alias for sudo-rs"),
    (r"(^|[\s,!(])(sudoedit|list)\s*$", r"^,", "keyword as a name: reserved by C, a name or alias for sudo-rs"),
    (r",\s*$", r"^[):]", "runas: trailing ',' accepted by sudo-rs"),
    (r":\s*$", r"^\)", "runas: empty list after ':' accepted by sudo-rs"),
    (r"/[ \t]+[^,:()]*$", r"", "command: directory with arguments rejected by C"),
    (r"\blist\s+$", r"", "command: 'list' with arguments rejected by C"),
    (r"/[^\s=,]*$", r"^=", "command: '=' inside a path (C ends the path there)"),
    (r"!\s+$", r"", "negation: '!' separated by whitespace rejected by C"),
]


def classify_c(cm, text, logical):
    """A line where C reports cm = (line, col, msg) and sudo-rs accepts."""
    line, col, msg = cm
    errno_only = msg.strip() in ERRNO_TEXT
    if not errno_only:
        for pat, cat in C_RULES:
            if re.search(pat, msg):
                return cat
    if line is not None:
        ltext0 = text.split("\n")[line - 1] if line - 1 < len(text.split("\n")) else ""
        if re.match(r"\s*Defaults[A-Za-z0-9_]", ltext0):
            return "Defaults keyword glued to a word: a user name for C, a Defaults line for sudo-rs"
    if (msg != "syntax error" and not errno_only) or line is None:
        return None
    lines = text.split("\n")
    ltext = lines[line - 1] if line - 1 < len(lines) else ""
    before, at = ltext[:col - 1], ltext[col - 1:]
    for b, a, cat in C_CONTEXT_RULES:
        if re.search(b, before) and re.search(a, at):
            return cat
    if "\\\n" in logical:
        return "continuation: inside a token (C joins or splits differently)"
    ch = at[:1]
    cc = char_class(ch)
    if cc:
        return "token class: " + cc + " (C stops)"
    return f"token class: C stops at '{ch}' where sudo-rs continues"


def cjoin(cerr):
    return "; ".join(m[2] for m in cerr)


# C messages that are the text of the current `errno` rather than a diagnostic (visudo prints
# them when the parser reports an error without a message of its own).
ERRNO_TEXT = {"Success", "No such file or directory", "File exists", "Is a directory",
              "Not a directory", "Permission denied", "Too many levels of symbolic links"}


# --------------------------------------------------------------------------- content

ALIAS = re.compile(r"^[A-Z][A-Z0-9_]*$")


def canon_marker(kind, args):
    """The argument mode that the kind and the argument list already imply: `""` (no further
    arguments) for an exact command with no argument, `*` (further arguments allowed) for a
    prefix with arguments, nothing otherwise. Both readers print one of these markers; keeping
    the canonical form only lets the two sides meet without carrying the printing convention."""
    if kind == "exact" and not args:
        return '""'
    if kind == "prefix" and args:
        return "*"
    return ""


def rs_cmd(c):
    path = S(c[1])
    kind, args = c[2][0], tuple(S(a) for a in c[2][1])
    return ("cmd", path, (kind, args, canon_marker(kind, args)))


def c_cmd(s):
    """C JSON command string -> the key of rs_cmd. C prints the command word and its arguments
    as it lexed them, a final `*` (further arguments allowed) or `""` (none) as a marker, and a
    path ending in `/` (any command in that directory). The marker is kept so that the modelling
    of C's word splitting (`c_word_join`) can recompute the argument mode."""
    parts = s.split()
    path, rest = parts[0], parts[1:]
    marker = args_marker = ""
    if rest and rest[-1] in ('""', "*"):
        marker, rest = rest[-1], rest[:-1]
        args_marker = marker
    kind = "prefix" if marker == "*" else ("exact" if rest or marker == '""' else "prefix")
    marker = canon_marker(kind, rest)
    if marker == "" and args_marker == '""' and rest and rest[0].startswith(("=", "\\")):
        marker = '""'  # a piece that c_word_join merges back: the marker then matters
    if path.endswith("/") and path != "/":
        path += "*"  # any command in that directory
    return ("cmd", path, (kind, tuple(rest), marker))


def rs_user(t):
    kind, ident = t[0], t[1]
    if ident[0] == "name":
        return ({"user": "username", "group": "usergroup",
                 "nonunix": "nonunixgroup"}[kind], S(ident[1]))
    return ({"user": "userid", "group": "usergid", "nonunix": "nonunixgid"}[kind], int(ident[1]))


def rs_spec(sp, f):
    neg = sp[0] == "forbid"
    m = sp[1]
    if m == "all":
        return (neg, "ALL")
    if m[0] == "alias":
        return (neg, ("alias", S(m[1])))
    return (neg, f(m[1]))


def c_spec(d, cmd=False):
    neg = bool(d.get("negated"))
    for k, v in d.items():
        if k == "negated":
            continue
        if k in ("useralias", "runasalias", "hostalias", "cmndalias"):
            return (neg, ("alias", v))
        if v == "ALL" and k in ("username", "hostname", "command"):
            return (neg, "ALL")
        if k in ("username", "hostname") and ALIAS.match(str(v)):
            return (neg, ("alias", v))  # cvtsudoers prints alias references by member kind
        if k == "command":
            return (neg, c_cmd(v))
        if k in ("userid", "usergid", "nonunixgid"):
            return (neg, (k, int(v)))
        if k.startswith(("sha", "digest")):
            return (neg, ("digest", k))
        return (neg, (k, v))
    return (neg, "?")


def srt(xs):
    return tuple(sorted(xs, key=repr))


def rs_setting_name(setting):
    tag, name, _ = setting
    if tag != "setting" or not isinstance(name, str):
        raise ValueError("expected a version 2 setting record")
    return name


def rs_entries(items):
    out = []
    for it in items:
        t = sexp(it)
        if t == "comment":
            continue
        tag = t[0]
        if tag == "spec":
            users = srt(rs_spec(u, rs_user) for u in t[1])
            for perm in t[2]:
                hosts = srt(rs_spec(h, lambda x: ("hostname", S(x))) for h in perm[1])
                cmds = srt(rs_spec(e[3], rs_cmd) for e in perm[2])
                out.append(("rule", users, hosts, cmds))
        elif tag.endswith("_alias"):
            f = {"user_alias": rs_user, "runas_alias": rs_user,
                 "host_alias": lambda x: ("hostname", S(x)), "cmnd_alias": rs_cmd}[tag]
            for d in t[1]:
                out.append((tag, S(d[1]), srt(rs_spec(x, f) for x in d[2])))
        elif tag == "defaults":
            names = srt(rs_setting_name(s) for s in t[2])
            out.append(("defaults", rs_scope(t[1]), names))
    return out


def rs_scope(s):
    if s == "generic":
        return ("generic",)
    f = {"host": lambda x: ("hostname", S(x)), "user": rs_user, "runas": rs_user,
         "command": lambda x: rs_cmd(("cmd", x, ("prefix", [])))}[s[0]]
    # cvtsudoers JSON does not record whether a user binding is ':' or '>'
    kind = "user|runas" if s[0] in ("user", "runas") else s[0]
    return (kind, srt(rs_spec(x, f) for x in s[1]))


def c_entries(js):
    out = []
    for us in js.get("User_Specs", []):
        users = srt(c_spec(u) for u in us["User_List"])
        hosts = srt(c_spec(h) for h in us["Host_List"])
        cmds = srt(c_spec(c) for cs in us["Cmnd_Specs"] for c in cs["Commands"])
        out.append(("rule", users, hosts, cmds))
    for key, tag in (("User_Aliases", "user_alias"), ("Runas_Aliases", "runas_alias"),
                     ("Host_Aliases", "host_alias"), ("Command_Aliases", "cmnd_alias")):
        for name, members in js.get(key, {}).items():
            out.append((tag, name, srt(c_spec(m) for m in members)))
    for d in js.get("Defaults", []):
        b = d.get("Binding")
        if not b:
            scope = ("generic",)
        else:
            kinds = {k for m in b for k in m if k != "negated"}
            kind = ("host" if kinds & {"hostname", "hostalias", "networkaddr"} else
                    "command" if kinds & {"command", "cmndalias"} else "user|runas")
            scope = (kind, srt(c_spec(m) for m in b))
        names = srt(k for o in d.get("Options", []) for k in o if k != "operation")
        out.append(("defaults", scope, names))
    return out


def canonicalize(path):
    """common::resolve::canonicalize: canonical parent joined with the file name, if the result
    exists (Rust `Path` component rules: '.' and empty components dropped, a final '..' has no
    file name)."""
    comps = [c for c in path.split("/") if c not in ("", ".")]
    if not comps:
        return path
    last, parent = comps[-1], "/" + "/".join(comps[:-1])
    if not os.path.isdir(parent):
        return None
    real = os.path.realpath(parent)
    res = real if last == ".." else os.path.join(real, last)
    return res if os.path.exists(res) else None


def c_canon(entry_part):
    """C keeps command paths as written; sudo-rs canonicalizes existing ones when parsing (by
    convention only the fixture's paths exist)."""
    neg, x = entry_part
    if isinstance(x, tuple) and x[0] == "cmd" and x[1].startswith("/"):
        p = x[1]
        if p.endswith("/*"):
            r = canonicalize(p[:-2])
            p = r + "/*" if r else p
        else:
            p = canonicalize(p) or p
        return (neg, ("cmd", p, x[2]))
    return entry_part


def map_parts(e, f):
    """Apply f to every member of an entry."""
    if e[0] == "rule":
        return ("rule", srt(map(f, e[1])), srt(map(f, e[2])), srt(map(f, e[3])))
    if e[0].endswith("_alias"):
        return (e[0], e[1], srt(map(f, e[2])))
    if e[0] == "defaults" and e[1] != ("generic",):
        return ("defaults", (e[1][0], srt(map(f, e[1][1]))), e[2])
    return e


def c_id_names(part):
    neg, x = part
    if isinstance(x, tuple) and x[0] in ("username", "usergroup", "nonunixgroup") and \
            re.fullmatch(r"#\d+", str(x[1])) and int(x[1][1:]) < 2 ** 32:
        k = {"username": "userid", "usergroup": "usergid", "nonunixgroup": "nonunixgid"}[x[0]]
        return (neg, (k, int(x[1][1:])))
    return part


def c_word_join(part):
    """C's lexer splits a word at an unescaped `=` and after an escape: it prints the pieces as
    separate words (`/a`, `=b`, `c`, `\\d`). sudo-rs keeps them in one path or argument. Join a
    piece that starts with `=` or a backslash onto the piece before it and recompute whether
    further arguments are allowed."""
    neg, x = part
    if not (isinstance(x, tuple) and x[0] == "cmd"):
        return part
    kind, args, marker = x[2]
    words = [x[1]] + list(args)
    merged = [words[0]]
    for w in words[1:]:
        if w.startswith(("=", "\\")):
            merged[-1] += w
        else:
            merged.append(w)
    path, args = merged[0], tuple(merged[1:])
    kind = "prefix" if marker == "*" else ("exact" if args or marker == '""' else "prefix")
    return (neg, ("cmd", path, (kind, args, canon_marker(kind, args))))


def rs_colon_group(part):
    """A quoted `"%:Name"` never reaches sudo-rs's non-unix branch: it re-parses the text with
    `:` escaped, so the `%` is read as a Unix group whose name starts with `:`."""
    neg, x = part
    if isinstance(x, tuple) and x[0] == "usergroup" and str(x[1]).startswith(":"):
        return (neg, ("nonunixgroup", x[1][1:]))
    return part


def split_path_space(part):
    """C's lexer ends a command word at an escaped space: `a\\ b` is printed as two words. Model
    both readings in one form by moving a path's first space and what follows into the argument
    list."""
    neg, x = part
    if isinstance(x, tuple) and x[0] == "cmd" and " " in x[1]:
        head, rest = x[1].split(" ", 1)
        kind, args, marker = x[2]
        return (neg, ("cmd", head, (kind, (rest,) + args, marker)))
    return part


def binding_path_join(part):
    """A `Defaults!` binding is a command pattern for sudo-rs, which carries no arguments; C
    reads the same text as a path with an argument list. Put both readings in one form: the
    words joined by single spaces, no arguments."""
    neg, x = part
    if isinstance(x, tuple) and x[0] == "cmd":
        words = [x[1]] + list(x[2][1])
        return (neg, ("cmd", " ".join(words), ("prefix", (), "")))
    return part


def rs_quoted_all(part):
    neg, x = part
    if x == ("username", "ALL"):
        return (neg, "ALL")
    return part


def rs_nonunix_gid(part):
    neg, x = part
    if isinstance(x, tuple) and (x[0] in ("nonunixgid", "nonunixgroup") or
                                 (x[0] == "usergroup" and str(x[1]).startswith(":"))):
        return (neg, ("nonunixgid", None))
    return part


def c_nonunix_gid(part):
    neg, x = part
    if isinstance(x, tuple) and x[0] == "nonunixgid":
        return (neg, ("nonunixgid", None))
    return part


def rs_quoted_alias(part):
    neg, x = part
    if isinstance(x, tuple) and x[0] == "username" and ALIAS.match(str(x[1])):
        return (neg, ("alias", x[1]))
    return part


def c_hash_rule(e):
    """A rule C keeps whose first user is a `#` id of more than ten digits or above `u32::MAX`:
    after `#` sudo-rs reports the token as too large or too long and then reads the line as a
    comment (F-P4)."""
    if e[0] != "rule" or not e[1]:
        return e
    _, part = e[1][0]
    if isinstance(part, tuple) and part[0] in ("username", "usergroup"):
        name = str(part[1])
        if re.fullmatch(r"#\d+", name) and (len(name) - 1 > 10 or int(name[1:]) > 0xFFFFFFFF):
            return None
    return e


# (category, transformation of sudo-rs entries, transformation of C entries); an entry
# transformed to None is dropped. Tried one at a time, then all together.
EXPLANATIONS = [
    ("F-P5: command path canonicalized by sudo-rs at parse time", None, lambda e: map_parts(e, c_canon)),
    ("user id: '#N' that C reads as a name, sudo-rs as an id", None, lambda e: map_parts(e, c_id_names)),
    ("F-P4: '#' line read as a comment by sudo-rs, a rule for C", None, c_hash_rule),
    ("quoted '%:' group: sudo-rs reads a Unix group whose name starts with ':'",
     lambda e: map_parts(e, rs_colon_group), None),
    ("command: C splits a word at '=' or after an escape, sudo-rs keeps it whole",
     None, lambda e: map_parts(e, c_word_join)),
    ("command: C ends a command word at an escaped space, sudo-rs keeps it in the path",
     lambda e: map_parts(e, split_path_space), lambda e: map_parts(e, split_path_space)),
    ("Defaults! binding: sudo-rs reads a command pattern, C a path with an argument list",
     lambda e: map_parts(e, binding_path_join), lambda e: map_parts(e, binding_path_join)),
    ('quoted "ALL": the ALL keyword for C, a name for sudo-rs',
     lambda e: map_parts(e, rs_quoted_all), None),
    ("quoted '%:#N': sudo-rs and C read the non-unix group name differently",
     lambda e: map_parts(e, rs_nonunix_gid), lambda e: map_parts(e, c_nonunix_gid)),
    ("quoted upper-case word: a user name for sudo-rs, an alias for C",
     lambda e: map_parts(e, rs_quoted_alias), None),
]


# Explanations that replace a name by a placeholder; used only when no explanation that keeps
# the form of an entry explains the difference.
LOSSY = {"quoted '%:#N': sudo-rs and C read the non-unix group name differently",
         "command: C ends a command word at an escaped space, sudo-rs keeps it in the path",
         "Defaults! binding: sudo-rs reads a command pattern, C a path with an argument list"}


def apply(f, entries):
    if f is None:
        return collections.Counter(entries)
    return collections.Counter(x for x in (f(e) for e in entries.elements()) if x is not None)


def part_cause(x, y):
    """Name the difference between two members of a list, or two commands."""
    if not (isinstance(x, tuple) and isinstance(y, tuple)) or x == y or len(x) < 2 or len(y) < 2:
        return None
    xs, ys = x[1], y[1]
    if (xs, ys) in ((("username", "ALL"), "ALL"), ("ALL", ("username", "ALL"))):
        return 'quoted "ALL": the ALL keyword for C, a user name for sudo-rs'
    if isinstance(xs, tuple) and isinstance(ys, tuple) and len(xs) >= 2 and len(ys) >= 2:
        if (xs[0] == "alias" and ys == "ALL") or (xs == "ALL" and ys[0] == "alias"):
            return 'quoted "ALL": the ALL keyword for C, an alias reference for sudo-rs'
        if {xs[0], ys[0]} == {"nonunixgid", "nonunixgroup"} and (
                (xs[0] == "nonunixgid" and xs[1] is None) or (ys[0] == "nonunixgid" and ys[1] is None)
                or (xs[0] == "nonunixgroup" and xs[1] == "")
                or (ys[0] == "nonunixgroup" and ys[1] == "")):
            return ("quoted '%:' group: sudo-rs reads no non-unix group name, C reads the name "
                    "(or a gid)")
        if {xs[0], ys[0]} == {"userid", "username"}:
            n, name = (xs[1], ys[1]) if xs[0] == "userid" else (ys[1], xs[1])
            if isinstance(name, str) and name.startswith("#" + str(n)):
                return ("quoted user id: sudo-rs keeps the leading '#N', C keeps the rest of "
                        "the text")
        if xs[0] == ys[0] and xs[0] in ("username", "usergroup", "nonunixgroup", "hostname") \
                and isinstance(xs[1], str) and isinstance(ys[1], str):
            short, long = (xs[1], ys[1]) if len(xs[1]) < len(ys[1]) else (ys[1], xs[1])
            if short and long.startswith(short):
                return ("quoted name: sudo-rs keeps the part before a character its unquoted "
                        "token does not accept")
        if xs[0] == ys[0] == "cmd" and xs[1] != ys[1] and \
                (ys[1].startswith(xs[1]) or xs[1].startswith(ys[1])):
            return "command path: C ends the path at the escape or '=', sudo-rs keeps it"
        if xs[0] == ys[0] == "cmd" and xs[1] != ys[1] and \
                xs[1].split(" ") + list(xs[2][1]) == ys[1].split(" ") + list(ys[2][1]):
            return ("command: the same words, C splits at an escaped space and sudo-rs keeps "
                    "the space in the path")
    return None


def member_cause(only_rs, only_c):
    """Name the first differing member of unmatched entries of the same kind."""
    for e in only_rs:
        for f in only_c:
            if e[0] == f[0] == "defaults" and e[1][0] == f[1][0]:
                for u in e[1][1]:
                    for v in f[1][1]:
                        cat = part_cause(u, v)
                        if cat:
                            return cat
                continue
            if e[0] != f[0] or len(e) != len(f):
                continue
            for i in range(1, len(e)):
                if e[:i] != f[:i] or e[i + 1:] != f[i + 1:]:
                    continue
                x, y = e[i], f[i]
                for u in (x if isinstance(x, tuple) else [x]):
                    for v in (y if isinstance(y, tuple) else [y]):
                        cat = part_cause(u, v)
                        if cat:
                            return cat
    return None


def content_category(mine, theirs, text):
    """Name the cause of a content difference: the explanation that makes both sides equal, else
    the first differing member of the unmatched entries, else the text."""
    for name, frs, fc in EXPLANATIONS:
        if apply(frs, mine) == apply(fc, theirs):
            return name
    # Several causes in one text: first the explanations that keep the form of an entry (the
    # '%:' ones replace a name by a placeholder and are only used when nothing else fits).
    for keep in (False, True):
        a, b = mine, theirs
        for name, frs, fc in EXPLANATIONS:
            if keep and name in LOSSY:
                continue
            a, b = apply(frs, a), apply(fc, b)
        if a == b:
            return "content: several of the causes above"
    only_rs, only_c = list(a - b), list(b - a)
    cat = member_cause(only_rs, only_c)
    if cat:
        return cat
    if [e for e in only_c if e[0] == "rule"] and not [e for e in only_rs if e[0] == "rule"] and \
            re.search(r"(^|[\n])[ \t]*#(?!include|includedir)", text):
        return "F-P4: '#' line read as a comment by sudo-rs, a rule for C"
    if only_c and not only_rs and \
            re.search(r"(^|[\n])[ \t]*#[^\n]*\\[\n]", text):
        return ("comment ending in a backslash: sudo-rs loses the next line, C keeps it")
    for e in only_rs:
        for f in only_c:
            if e[0] == f[0] == "rule" and e[1] == f[1] and e[2] == f[2]:
                return "unclassified content: rule commands differ"
            if e[0] == f[0] == "rule" and e[1] == f[1]:
                return "unclassified content: rule hosts differ"
            if e[0] == f[0] == "rule":
                return "unclassified content: rule users differ"
            if e[0] == f[0] and e[0].endswith("_alias") and e[1] == f[1]:
                return f"unclassified content: {e[0]} members differ"
            if e[0] == f[0] == "defaults":
                return "unclassified content: Defaults differ"
    kinds = sorted({e[0] for e in only_rs} | {e[0] for e in only_c})
    return "unclassified content: " + "/".join(kinds) + " entries differ"


# --------------------------------------------------------------------------- main


def category_of(label):
    c = label.split(":")[0]
    return "mut." + c.split(".")[1] if c.startswith("mut.") else c


def main():
    corpus = read_corpus(sys.argv[1])
    if not corpus:
        raise SystemExit(f"{sys.argv[1]}: no cases")
    dump = read_dump(sys.argv[2])
    cres = read_c(sys.argv[3])
    hostdep = read_hostdep(sys.argv[2] + ".hostdep")
    advisories = advisory_shapes(list(cres.values()))
    details = open(sys.argv[4], "w", encoding="utf-8") if len(sys.argv) > 4 else None

    accept = collections.Counter()
    diff = collections.Counter()
    diff_cases = collections.defaultdict(set)
    agree = collections.Counter()
    content = collections.Counter()
    inconsistent = []
    by_cat = collections.Counter()
    acct = collections.Counter()
    acct_cases = collections.defaultdict(list)
    rows = collections.Counter()

    def note(label, cat, line, info, ll=None):
        diff[cat] += 1
        diff_cases[cat].add(label)
        if ll is not None:
            rows[ll] += 1
        if details:
            info = str(info).replace("\t", " ").replace("\n", " ")
            details.write(f"{label}\t{line}\t{cat}\t{info}\n")

    for label, text in corpus:
        by_cat[category_of(label)] += 1
        recs = dump[label]
        c = cres[label]
        if any(r.startswith("panic ") for r in recs):
            note(label, "sudo-rs panics", 0, "")
            continue
        rs_clean = not any(r.startswith("fatal ") for r in recs)
        c_clean = c["visudo"][0] == 0
        accept[(rs_clean, c_clean)] += 1
        start, lines = logical_lines(text)
        its, ok = rs_iterations(recs, text)
        if not ok:
            inconsistent.append(label)
        rows = collections.Counter()
        rs_diag = collections.Counter()      # logical lines where sudo-rs reports something
        agreed_lines = set()                 # both sides report something on the line
        handled_lines = set()
        skipped = collections.Counter()      # named reason why no row is needed on a line
        c_err = collections.defaultdict(list)
        c_adv = collections.defaultdict(list)
        c_unplaced = []
        for line, col, msg, sev in c_messages(c, text):
            if sev == "error" and msg_shape(msg) in advisories:
                sev = "advisory"  # the shape occurs in files visudo accepted: not a rejection
            if sev == "warning":
                continue
            if line is None:
                if sev == "error":
                    c_unplaced.append((line, col, msg))
            elif sev == "advisory":
                c_adv[start.get(line, line)].append((line, col, msg))
            else:
                c_err[start.get(line, line)].append((line, col, msg))

        def first_c(cerr, logical):
            for cm in cerr:
                cat = classify_c(cm, text, logical)
                if cat:
                    return cat
            return None

        for it in its:
            if it.get("artifact"):
                continue
            L = it["line"]
            LL = start.get(L, L)
            mid = LL != L
            cerr = c_err.get(LL, [])
            logical = logical_text(lines, start, LL)
            kind = it["kind"]
            if kind == "error":
                rs_diag[LL] += 1
                if mid and (rows[LL] or LL in agreed_lines):
                    # the rest of a logical line that already produced a row or an agreement
                    skipped["F-P2: rest of a logical line that already has a row"] += 1
                    continue
                if cerr:
                    agree["both reject the line"] += 1
                    agreed_lines.add(LL)
                    continue
                cat = classify_rs(it["msg"], text, it["span"], logical, L)
                note(label, cat or "unclassified: sudo-rs rejects, C accepts", LL, it["msg"], LL)
            elif kind == "item":
                ek = sexp(it["item"])[0]
                ek = "rule" if ek == "spec" else ek
                if mid:
                    note(label, "F-P2: sudo-rs reads the continuation of a failed line as a line of its own", LL, it["item"][:80], LL)
                    continue
                g = it["garbage"]
                if g:
                    rs_diag[LL] += 1
                if g and g[1].startswith("missing line terminator"):
                    if cerr:
                        agree["both reject the line"] += 1
                        agreed_lines.add(LL)
                    else:
                        note(label, "end of file: last line without newline", LL, "", LL)
                    continue
                if g:
                    if cerr:
                        agreed_lines.add(LL)
                        if ek.endswith("_alias"):
                            # testsudoers -d prints the definitions C kept
                            name = S(sexp(it["item"])[1][0][1])
                            kept = re.search(r"\b" + re.escape(name) + r"\s*=", c["ts"][1]) is not None
                            how = "C keeps the prefix too" if kept else "C keeps nothing"
                        else:
                            how = "C reports an error"
                        note(label, f"F-P1: prefix acceptance ({ek}; {how})", LL, cjoin(cerr), LL)
                    else:
                        cat = classify_rs("", text, g[0], logical, L)
                        note(label, cat or "unclassified: sudo-rs stops early, C accepts", LL, g[1], LL)
                    continue
                if cerr:
                    note(label, first_c(cerr, logical) or "unclassified: C rejects, sudo-rs accepts", LL, cjoin(cerr), LL)
                else:
                    agree[f"both accept ({ek})"] += 1
            elif kind == "comment":
                g = it["garbage"]
                if g:
                    rs_diag[LL] += 1
                    if cerr:
                        agree["both reject the line"] += 1
                        agreed_lines.add(LL)
                        continue
                    if g[1].startswith("missing line terminator"):
                        note(label, "end of file: last line without newline", LL, "", LL)
                        continue
                    cat = classify_rs("", text, g[0], logical, L)
                    note(label, cat or "unclassified: sudo-rs reads nothing, C accepts", LL, g[1], LL)
                elif cerr and not mid:
                    agreed_lines.add(LL)
                    lt = lines[L - 1] if L - 1 < len(lines) else ""
                    if lt.lstrip().startswith("#"):
                        note(label, "F-P4: '#' line read as a comment by sudo-rs, rejected by C", LL, cjoin(cerr), LL)
                    else:
                        note(label, first_c(cerr, logical) or "unclassified: C rejects a line sudo-rs reads as empty",
                             LL, cjoin(cerr), LL)
            elif kind == "panic":
                note(label, "sudo-rs panics", L, it["msg"])
        for LL, cadv in c_adv.items():
            if LL in c_err or LL in agreed_lines or rows[LL]:
                continue
            logical = logical_text(lines, start, LL)
            note(label, first_c(cadv, logical) or "unclassified: C advisory without a category",
                 LL, cjoin(cadv), LL)
        for LL, cerr in c_err.items():
            if LL in agreed_lines or rows[LL]:
                continue
            logical = logical_text(lines, start, LL)
            note(label, first_c(cerr, logical) or "unclassified: C rejects a line without sudo-rs item",
                 LL, cjoin(cerr), LL)
        for cm in c_unplaced:
            note(label, classify_c(cm, text, "") or "unclassified: C error without a line", 0, cm[2], 0)

        # Accounting: the case and line invariants of the comparator itself.
        fatal = any(r.startswith("fatal ") for r in recs)
        c_reject = c["visudo"][0] != 0
        if fatal != c_reject and sum(rows.values()) == 0:
            acct["cases: diagnostics on one side only, no row"] += 1
            acct_cases["case: no row"].append(label)
        for LL in sorted(set(rs_diag) ^ set(c_err)):
            if rows[LL] or skipped[LL]:
                continue
            acct["lines: one side reports, the other does not, no row"] += 1
            acct_cases["line: no row"].append(f"{label}:{LL}")
        if rs_clean and c_clean and c.get("cvt") and c["cvt"][0] == 0:
            items = [r[3:] for r in recs if r.startswith("ok ")]
            mine = collections.Counter(rs_entries(items))
            js = json.loads(c["cvt"][1]) if c["cvt"][1].strip() else {}
            theirs = collections.Counter(c_entries(js))
            content["compared"] += 1
            if mine == theirs:
                content["equal"] += 1
            else:
                only_rs, only_c = list(mine - theirs), list(theirs - mine)
                cat = content_category(mine, theirs, text)
                if label in hostdep and cat.startswith(("unclassified", "content: several")):
                    cat = ("comparison limit: the case names an existing host path, so the "
                           "pattern can be canonicalized on one host only (hostdep)")
                note(label, cat, 0,
                     f"sudo-rs only: {only_rs[:2]} C only: {only_c[:2]}", 0)

    n = len(corpus)
    print(f"cases: {n}; iteration reconstruction inconsistent: {len(inconsistent)} {inconsistent[:5]}\n")
    print("| corpus category | cases |\n|---|---|")
    for k in sorted(by_cat):
        print(f"| {k} | {by_cat[k]} |")
    print("\n| sudo-rs | C sudo (`visudo -c`) | cases |\n|---|---|---|")
    for (r, cc), v in sorted(accept.items(), reverse=True):
        print(f"| {'no diagnostic' if r else 'diagnostics'} | {'accepted' if cc else 'rejected'} | {v} |")
    print("\n| agreement | lines |\n|---|---|")
    for k, v in sorted(agree.items()):
        print(f"| {k} | {v} |")
    print(f"\nEntries compared with `cvtsudoers -f json` (both accept the file): {content['compared']} "
          f"cases, {content['equal']} equal.\n")
    print("| difference category | differences | cases |\n|---|---|---|")
    for k, v in sorted(diff.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"| {k} | {v} | {len(diff_cases[k])} |")
    unclassified = sum(v for k, v in diff.items() if k.startswith("unclassified"))
    print(f"\ndifferences: {sum(diff.values())}; unclassified: {unclassified}")
    print(f"\naccounting: case violations {acct['cases: diagnostics on one side only, no row']}, "
          f"line violations {acct['lines: one side reports, the other does not, no row']}")
    for reason, n in sorted(skipped.items()):
        print(f"  counted reason for a line without a row: {n}  {reason}")
    violations = acct["cases: diagnostics on one side only, no row"] + \
        acct["lines: one side reports, the other does not, no row"]
    for k in ("case: no row", "line: no row"):
        if acct_cases[k]:
            print(f"  {k}: {', '.join(sorted(set(acct_cases[k]))[:10])}")
    if violations:
        sys.exit(1)
    print(f"\nadvisory message shapes (occur in files `visudo -c` accepted, so never a rejection):")
    for shape, n in sorted(advisories.items()):
        print(f"  {n:6d}  {shape}")
    print("\n## Fixed inputs (PLAN.md section 3.3, F-P1 to F-P6)\n")
    for label, text in corpus:
        if not label.startswith("known:"):
            continue
        c = cres[label]
        rs = []
        for r in dump[label]:
            if r.startswith("fatal "):
                m = FATAL.match(r)
                rs.append(f"fatal {m.group(1)}:{m.group(2)} {unquote(m.group(5))[0]}")
            elif r == "ok comment":
                rs.append("comment")
            elif r.startswith("ok "):
                t = sexp(r[3:])
                rs.append(summary(t))
        kept = [l for l in c["ts"][1].split("\n") if l and l != "Parses OK"]
        cmsg = [f"{m[0]}:{m[1]} {m[2]}" for m in c_messages(c, text) if m[3] == "error"]
        print(f"- `{json.dumps(text)[1:-1]}`")
        print(f"  - sudo-rs: {'; '.join(rs)}")
        print(f"  - C sudo: {'accepted' if c['visudo'][0] == 0 else 'rejected'}"
              f"{' (' + '; '.join(cmsg) + ')' if cmsg else ''}; kept: {' / '.join(kept) or 'nothing'}")
    if details:
        details.close()


def summary(t):
    """A short description of a dump item."""
    if t[0] == "spec":
        users = ",".join(describe(u) for u in t[1])
        cmds = ",".join(describe(e[3]) for p in t[2] for e in p[2])
        return f"rule {users} -> {cmds}"
    if t[0] == "defaults":
        return f"Defaults ({len(t[2])} settings)"
    if t[0].endswith("_alias"):
        return f"{t[0]} " + "; ".join(f"{S(d[1])} = {','.join(describe(x) for x in d[2])}" for d in t[1])
    return t[0]


def describe(sp):
    neg = "!" if sp[0] == "forbid" else ""
    m = sp[1]
    if m == "all":
        return neg + "ALL"
    if m[0] == "alias":
        return neg + S(m[1])
    x = m[1]
    if isinstance(x, tuple) and x[0] in ("user", "group", "nonunix"):
        return neg + ("" if x[0] == "user" else "%" if x[0] == "group" else "%:") + \
            (S(x[1][1]) if x[1][0] == "name" else "#" + x[1][1])
    if isinstance(x, tuple) and x[0] == "cmd":
        return neg + S(x[1])
    return neg + str(S(x))


if __name__ == "__main__":
    main()
