#!/usr/bin/env python3
"""Run the axiom audit and check it (standard library only).

Usage: python3 scripts/check-axioms.py [--core] [--root DIR] [--log FILE]

Elaborates `scripts/Axioms.lean` (with `--core`: `scripts/AxiomsCore.lean`) with `lake env lean` from the
repository root and checks its `#print axioms` output: every theorem listed in the file is reported, each
depends only on `propext`, `Classical.choice` and `Quot.sound`, nothing else is reported, and Lean prints no
error. The project must be built first: `lake build` for `--core`, and `lake build SandierSerfatyCert` (about
14 CPU-hours) for the full list, which includes the five theorems that rest on the kernel certificate. Long
names make Lean wrap an axiom list over several lines, so the whole output is parsed, not single lines.

Exit status: 0 PASS, 1 FAIL.
"""
from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def parse_report(output: str) -> dict[str, set[str]]:
    found: dict[str, set[str]] = {}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        found[match.group(1)] = {a.strip() for a in match.group(2).split(",") if a.strip()}
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        found[match.group(1)] = set()
    return found


def check_report(expected: list[str], output: str) -> tuple[list[str], dict[str, set[str]]]:
    """Problems found in Lean's output for the expected theorem names."""
    problems: list[str] = []
    found = parse_report(output)
    if not expected:
        problems.append("the axiom file prints the axioms of no theorem")
    for name in expected:
        if name not in found:
            problems.append(f"{name}: no axiom report")
        elif not found[name] <= ALLOWED:
            problems.append(f"{name}: axioms beyond the standard three: {sorted(found[name] - ALLOWED)}")
    extra = sorted(set(found) - set(expected))
    if extra:
        problems.append(f"unexpected reports: {extra}")
    for line in output.splitlines():
        if re.search(r":\d+:\d+: error", line) or line.startswith("error:"):
            problems.append(f"Lean error: {line.strip()}")
    return problems, found


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--core", action="store_true", help="check the eight core theorems only (scripts/AxiomsCore.lean)")
    parser.add_argument("--log", type=Path, help="also write Lean's output to this file")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    name = "AxiomsCore.lean" if args.core else "Axioms.lean"
    source = root / "scripts" / name
    if not source.is_file():
        print(f"check-axioms: FAIL (scripts/{name} is missing)")
        return 1
    if shutil.which("lake") is None:
        print("check-axioms: FAIL (lake is not on PATH)")
        return 1
    expected = re.findall(r"(?m)^#print[ \t]+axioms[ \t]+(\S+)", source.read_text(encoding="utf-8"))
    done = subprocess.run(["lake", "env", "lean", f"scripts/{name}"], cwd=root, capture_output=True, text=True)
    output = done.stdout + done.stderr
    if args.log:
        args.log.write_text(output, encoding="utf-8")
    problems, found = check_report(expected, output)
    if done.returncode and not any(p.startswith("Lean error") for p in problems):
        problems.append(f"lean exited with status {done.returncode}")
    for theorem in expected:
        if theorem in found and found[theorem] <= ALLOWED:
            print(f"ok   {theorem}: {sorted(found[theorem])}")
    for problem in problems:
        print(f"FAIL {problem}")
    print(f"check-axioms: {'FAIL' if problems else 'PASS'} ({len(expected)} theorems checked)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
