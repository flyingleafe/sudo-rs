#!/usr/bin/env python3
"""Pattern-level comparison of env_keep/env_check entries: sudo-rs `entry_matches`
(src/sudo/env/filter.rs) against C sudo's `matches_env_pattern` (plugins/sudoers/env_pattern.c),
run through C sudo's own unprivileged regress checker `check_env_pattern`.

This compares the matching of one entry against one variable only, not the filtering decision
(value checks, TZ, precedence) or assembly.

  env_pattern.py gen DIR            write DIR/rust.tsv (ENTRY<TAB>NAME<TAB>VALUE) and
                                    DIR/c.txt (`ENTRY NAME=VALUE 0`, the checker's format)
  env_pattern.py compare DIR OUT RC validate DIR/rust.out, DIR/c.out, DIR/c.err and RC,
                                    then write OUT/summary.txt (aggregate counts only)

Patterns have length 1–4 and consist of a nonempty name pattern over {A, B, *}, optionally
followed by `=` and a value pattern over {A, B, *}. Names are length 1–3 over {A, B}, and
values are length 0–2 over {A, B, =}: 222 × 14 × 13 = 40,404 cases. They are passed as data to
an unprivileged checker, not installed in an environment.
"""
import itertools
import os
import re
import sys


def words(alphabet, lo, hi):
    for n in range(lo, hi + 1):
        for t in itertools.product(alphabet, repeat=n):
            yield "".join(t)


def cases():
    for entry in words("AB*=", 1, 4):
        if entry.startswith("=") or entry.count("=") > 1:
            continue
        for name in words("AB", 1, 3):
            for value in words("AB=", 0, 2):
                yield entry, name, value


def gen(d):
    os.makedirs(d, exist_ok=True)
    n = 0
    with open(os.path.join(d, "rust.tsv"), "w") as r, open(os.path.join(d, "c.txt"), "w") as c:
        for entry, name, value in cases():
            r.write(f"{entry}\t{name}\t{value}\n")
            # `want` is 0 for every line: the checker reports exactly the lines that match
            # (result 1, or 2 for a match on the value too).
            c.write(f"{entry} {name}={value} 0\n")
            n += 1
    print(f"{n} cases")


LINE = re.compile(r": (\S+) (\S+): want 0, got ([0-9]+)$")


def compare(d, out, rc):
    all_cases = list(cases())
    known = {(e, f"{n}={v}") for e, n, v in all_cases}
    total = len(all_cases)
    with open(os.path.join(d, "rust.out")) as f:
        rust_lines = f.read().splitlines()
    if len(rust_lines) != total or any(line not in {"0", "1"} for line in rust_lines):
        sys.exit(f"expected {total} Boolean results from sudo-rs")
    rust = [line == "1" for line in rust_lines]
    c_match = set()
    with open(os.path.join(d, "c.err")) as f:
        for line in f:
            m = LINE.search(line.rstrip("\n"))
            if m is None or m[3] not in {"1", "2"}:
                sys.exit("unexpected checker diagnostic")
            pair = (m[1], m[2])
            if pair not in known or pair in c_match:
                sys.exit("checker reported unknown or duplicate case")
            c_match.add(pair)
    with open(os.path.join(d, "c.out")) as f:
        summary = re.fullmatch(r".+: (\d+) tests? run, (\d+) errors, \d+% success rate\n", f.read())
    reports = len(c_match)
    if (summary is None or (int(summary[1]), int(summary[2])) != (total, reports)
            or rc != reports % 256):
        sys.exit("checker did not finish all cases or returned inconsistent counts")
    buckets = {}
    agree = 0
    for (entry, name, value), r in zip(all_cases, rust):
        c = (entry, f"{name}={value}") in c_match
        agree += r == c
        kind = "NAME=VALUE entry" if "=" in entry else "NAME entry"
        stars = min(entry.count("*"), 2)
        key = (kind, f"{stars}{'+' if stars == 2 else ''} star(s)")
        total_bucket, rust_only, c_only = buckets.get(key, (0, 0, 0))
        buckets[key] = (total_bucket + 1, rust_only + (r and not c), c_only + (c and not r))
    lines = [
        f"cases {total}",
        f"checker reports {reports} (matches by C sudo)",
        f"sudo-rs matches {sum(rust)}",
        f"agree {agree}",
        f"disagree {total - agree}",
    ]
    for key, (n, rust_only, c_only) in sorted(buckets.items()):
        lines.append(f"  {' / '.join(key)}: {n} total, {rust_only} sudo-rs only, {c_only} C only")
    text = "\n".join(lines) + "\n"
    with open(os.path.join(out, "summary.txt"), "w") as f:
        f.write(text)
    print(text, end="")


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "gen":
        gen(sys.argv[2])
    elif len(sys.argv) == 5 and sys.argv[1] == "compare":
        compare(sys.argv[2], sys.argv[3], int(sys.argv[4]))
    else:
        sys.exit(__doc__)
