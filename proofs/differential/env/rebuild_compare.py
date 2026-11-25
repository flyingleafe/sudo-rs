#!/usr/bin/env python3
"""Compare the observed outputs of the two ordinary in-process environment fixtures."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
import re
import subprocess
import sys


class InputError(ValueError):
    pass


@dataclass
class Case:
    keep: list[str] = field(default_factory=list)
    check: list[str] = field(default_factory=list)
    secure_path: str = ""
    env: dict[str, str] = field(default_factory=dict)
    assigned: dict[str, str] = field(default_factory=dict)

    @property
    def keys(self):
        return self.env.keys() | self.assigned.keys() | ({"PATH"} if self.secure_path else set())

    @property
    def stratum(self):
        return "set" if self.assigned else "inherited"

    def origin(self, key, value):
        if self.assigned.get(key) == value:
            return "set"
        if key == "PATH" and self.secure_path and self.secure_path == value:
            return "secure_path"
        if self.env.get(key) == value:
            return "caller"
        return "other"


PATHS = {"/usr/bin:/bin", "/usr/local/bin:/usr/bin"}
PATTERN = re.compile(r"(?:SUDOENV_|sudoenv_)[A-Za-z0-9_*]+(?:=[A-Za-z0-9_*/%=-]*)?|TZ|PATH")
NAME = re.compile(r"SUDOENV_[A-Z0-9_]+|TZ|PATH")
VALUE = re.compile(r"[A-Za-z0-9_./%=-]*")
ORIGINS = ("caller", "secure_path", "set", "drop", "other", "error")


def ordinary(key, value):
    if key == "TZ":
        return value in {"UTC", "Europe/Amsterdam"}
    if key == "PATH":
        return value in PATHS
    return bool(NAME.fullmatch(key) and VALUE.fullmatch(value))


def parse_cases(path):
    cases = {}
    case = None
    for line in path.read_text(encoding="ascii").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        verb, _, data = line.partition(" ")
        if verb == "case":
            if not re.fullmatch(r"[a-z0-9-]+", data) or data in cases:
                raise InputError("invalid or duplicate fixture case")
            cases[data] = case = Case()
        elif case is None:
            raise InputError("invalid fixture header")
        elif verb in {"keep", "check"}:
            patterns = data.split()
            if not patterns or not all(PATTERN.fullmatch(p) for p in patterns):
                raise InputError("out-of-scope fixture pattern; neither implementation run")
            getattr(case, verb).extend(patterns)
        elif verb == "secure_path":
            if data not in PATHS or case.secure_path:
                raise InputError("out-of-scope or duplicate secure_path")
            case.secure_path = data
        elif verb in {"env", "set"}:
            key, sep, value = data.partition("=")
            dest = case.env if verb == "env" else case.assigned
            if not sep or not ordinary(key, value) or key in dest:
                raise InputError("out-of-scope or duplicate assignment; neither implementation run")
            dest[key] = value
        elif verb != "expect":
            raise InputError("invalid fixture directive")
        # Expectations are not used for selection, normalization, or comparison.

    if not cases or any(not case.keys for case in cases.values()):
        raise InputError("empty fixture or case with no observable keys")
    if any(case.assigned and (case.env or case.secure_path) for case in cases.values()):
        raise InputError("mixed inherited/assignment case; neither implementation run")
    return cases


def rust_results(path, cases):
    outcomes = {name: {} for name in cases}
    for line in path.read_text(encoding="ascii").splitlines():
        parts = line.split("\t")
        if len(parts) != 3:
            raise InputError("malformed Rust observation")
        name, key, origin = parts
        if name not in cases or key in outcomes[name] or origin not in ORIGINS:
            raise InputError("unknown or duplicate Rust observation")
        outcomes[name][key] = origin
    return outcomes


def c_result(driver, case):
    argv = [str(driver.resolve()), " ".join(case.keep), " ".join(case.check), case.secure_path]
    argv.extend(f"{key}={value}" for key, value in sorted(case.env.items()))
    argv.append("--")
    argv.extend(f"{key}={value}" for key, value in sorted(case.assigned.items()))
    argv.extend(("--", *sorted(case.keys)))
    run = subprocess.run(argv, env={"LC_ALL": "C"}, capture_output=True, encoding="ascii")
    if run.returncode != 0:
        raise InputError(f"exit_{run.returncode}")
    outcomes = {}
    for line in run.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) < 2 or parts[0] in outcomes:
            raise InputError("malformed_or_duplicate")
        key, status = parts[:2]
        if len(parts) == 2 and (status == "drop" or (key, status) == ("-", "error")):
            outcomes[key] = status
        elif len(parts) == 3 and status == "present":
            outcomes[key] = case.origin(key, parts[2])
        else:
            raise InputError("malformed_or_duplicate")
    return outcomes


def complete(observed, case):
    return (observed == {"-": "error"} and case.stratum == "set") or (
        observed.keys() == case.keys and "error" not in observed.values()
    )


def compare(cases, driver, rust_path):
    rust = rust_results(rust_path, cases)
    missing = mismatches = 0
    for stratum in ("inherited", "set"):
        names = [name for name, case in cases.items() if case.stratum == stratum]
        print(f"{stratum}_cases={len(names)}")
        print(f"{stratum}_fixture_keys={sum(len(cases[name].keys) for name in names)}")
        counts = {"c": Counter(), "rust": Counter()}
        c_errors = Counter()
        c_failed = rust_incomplete = compared = differing_cases = differing_rows = 0
        for name in names:
            case = cases[name]
            try:
                c = c_result(driver, case)
            except InputError as exc:
                c_errors[str(exc)] += 1
                c = {}
            except (OSError, UnicodeError):
                c_errors["io_or_encoding"] += 1
                c = {}
            good_c = complete(c, case)
            good_rust = complete(rust[name], case)
            c_failed += not good_c
            rust_incomplete += not good_rust
            if not good_c or not good_rust:
                continue
            compared += 1
            counts["c"].update(c.values())
            counts["rust"].update(rust[name].values())
            diff = sum(c.get(k) != rust[name].get(k) for k in c.keys() | rust[name].keys())
            differing_cases += diff != 0
            differing_rows += diff
        print(f"{stratum}_compared={compared}")
        print(f"{stratum}_c_failed_or_incomplete={c_failed}")
        for reason, count in sorted(c_errors.items()):
            print(f"{stratum}_c_{reason}={count}")
        print(f"{stratum}_rust_incomplete={rust_incomplete}")
        print(f"{stratum}_differing_cases={differing_cases}")
        print(f"{stratum}_differing_rows={differing_rows}")
        for implementation, totals in counts.items():
            for origin in ORIGINS:
                print(f"{stratum}_{implementation}_{origin}={totals[origin]}")
        if stratum == "inherited":
            required = ("caller", "drop")
        else:
            required = ("set", "error")
        covered = all(totals[origin] for totals in counts.values() for origin in required)
        print(f"{stratum}_required_coverage={int(covered)}")
        missing += c_failed + rust_incomplete + (not covered)
        missing += sum(totals["other"] for totals in counts.values())
        mismatches += differing_cases
    return 2 if missing else int(mismatches != 0)


def main():
    args = sys.argv[1:]
    if len(args) not in {1, 3}:
        print("usage: rebuild_compare.py CASES [C_DRIVER RUST_OBSERVATIONS]", file=sys.stderr)
        return 2
    try:
        cases = parse_cases(Path(args[0]))
        if len(args) == 1:
            print(f"fixture_cases={len(cases)}")
            print("excluded_fixture_cases=0")
            print("out_of_scope=PAM,login shells,host policy/identity,nonordinary data,command execution")
            return 0
        return compare(cases, Path(args[1]), Path(args[2]))
    except (InputError, OSError, UnicodeError) as exc:
        message = str(exc) if isinstance(exc, InputError) else "fixture I/O or encoding failure"
        print(f"comparison_error={message}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
