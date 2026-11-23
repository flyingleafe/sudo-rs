#!/usr/bin/env python3
"""Compare the parser dump of the Rust parser with the dump of the Lean reference parser.

    parser_lean_compare.py RUST_DUMP LEAN_DUMP [DIFFERENCES]

Both dumps are in the format of proofs/parser/DUMP.md: the header `parser-dump 2`, then per case
a line `case <label>` and its records. Cases are compared byte for byte. A case listed in
`RUST_DUMP.hostdep` (it names an existing host path, so its Rust dump depends on the host's
file system, which the Lean test oracle does not model) is counted apart. Prints a summary per
category (the label up to the first `:`); DIFFERENCES, if given, receives every disagreeing case
with both dumps. Exit status 1 if a case that is not host-dependent disagrees.
"""
import os
import sys
from collections import OrderedDict


def check_dump_header(f):
    if f.readline() != "parser-dump 2\n":
        raise SystemExit(f"{f.name}: expected parser-dump 2 header")


def read_dump(path):
    cases = OrderedDict()
    label = None
    with open(path, encoding="ascii") as f:
        check_dump_header(f)
        for line in f:
            if line.startswith("case "):
                label = line[5:].rstrip("\n")
                if label in cases:
                    raise SystemExit(f"{path}: duplicate case {label}")
                cases[label] = []
            elif label is None:
                raise SystemExit(f"{path}: record before the first case")
            else:
                cases[label].append(line)
    if not cases:
        raise SystemExit(f"{path}: no cases")
    return OrderedDict((k, "".join(v)) for k, v in cases.items())


def category(label):
    return label.split(":", 1)[0]


def main():
    if len(sys.argv) not in (3, 4):
        raise SystemExit(__doc__)
    rust_path, lean_path = sys.argv[1], sys.argv[2]
    rust, lean = read_dump(rust_path), read_dump(lean_path)
    hostdep = set()
    if os.path.exists(rust_path + ".hostdep"):
        with open(rust_path + ".hostdep", encoding="ascii") as f:
            hostdep = {line.split(" ", 1)[0] for line in f if line.strip()}
    if list(rust) != list(lean):
        missing = [k for k in rust if k not in lean] + [k for k in lean if k not in rust]
        raise SystemExit(f"the dumps have different cases, e.g. {missing[:5]}")

    stats = OrderedDict()
    diffs = []
    for label, r in rust.items():
        s = stats.setdefault(category(label), [0, 0, 0, 0])  # cases, agree, differ, hostdep-differ
        s[0] += 1
        if r == lean[label]:
            s[1] += 1
        elif label in hostdep:
            s[3] += 1
            diffs.append((label, True, r, lean[label]))
        else:
            s[2] += 1
            diffs.append((label, False, r, lean[label]))

    total = [sum(s[i] for s in stats.values()) for i in range(4)]
    records = sum(r.count("\n") for r in rust.values())
    print("| category | cases | agree | differ | differ (host-dependent) |")
    print("|---|---|---|---|---|")
    for cat, (n, a, d, h) in sorted(stats.items()):
        print(f"| {cat} | {n} | {a} | {d} | {h} |")
    print(f"| **total** | {total[0]} | {total[1]} | {total[2]} | {total[3]} |")
    print()
    print(f"{total[0]} cases, {records} records, {len(hostdep)} host-dependent cases")
    if len(sys.argv) == 4:
        with open(sys.argv[3], "w", encoding="ascii") as f:
            for label, host, r, l in diffs:
                f.write(f"case {label}{' (host-dependent)' if host else ''}\n")
                f.write("--- rust\n" + r + "--- lean\n" + l)
    return 1 if total[2] else 0


if __name__ == "__main__":
    sys.exit(main())
