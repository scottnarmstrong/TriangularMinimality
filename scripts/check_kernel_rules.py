#!/usr/bin/env python3
"""Kernel-rule lint of the certificate modules. Untrusted tooling: it flags source patterns that make
`decide +kernel` slow, vacuous or dependent on something other than the kernel; it proves nothing, and a pass
adds nothing to the trust base (the kernel checks every proof regardless).

    python3 scripts/check_kernel_rules.py [--root DIR] [FILE ...]

Scope: every `.lean` file under `SandierSerfaty/Certificate/` and `SandierSerfaty/CertData/` (or the FILEs
given). An optional library layout file `scripts/build_roots.json`, which a release checkout does not contain,
adds the modules of the certificate applications it lists. Exit status 1 if any finding, or if no certificate
module is found.

The rules are checked on the code with comments and string literals masked.

Rules for every certificate module:

  K1 decide    a Boolean check is discharged by `decide +kernel` only: no `native_decide`, no `decide +native`
               (both trust compiled code), no plain `decide` (evaluation by the elaborator's `Decidable`
               reduction, which is slow on large data), and no `rfl`/`by rfl` for a statement ending in
               `= true` or `= false`;
  K2 forcing   a `decide +kernel` statement ends in a comparison that forces its data, never a test that the
               kernel can decide structurally without evaluating the left side: `Nat.blt 0 (x + 1)`,
               `Nat.blt 0 (Nat.succ x)`, `Nat.ble 0 x`, `0 ≤ x` on naturals, `0 < x + 1`.

Rules for every definition of a module marked strict (a line `-- kernel-rules: strict`), the modules whose
definitions the kernel evaluates in a hot loop; a definition preceded by a line `-- kernel-rules: exempt
(<reason>)` is skipped:

  K3 nat       no `Int`/`ℤ` arithmetic or `Int` powers, no `Nat.sqrt`: the kernel accelerates `Nat`
               operations with GMP but not `Int` ones, and `Nat.sqrt` is defined by well-founded recursion,
               which the kernel does not unfold efficiently;
  K4 recursion no well-founded recursion (`termination_by`, `decreasing_by`, `partial`);
  K5 lets      no `let`: shared `let`s in interval code were measured about 13 times slower and hit deep
               recursion in the kernel; pass arguments explicitly;
  K6 prims     `Nat` primitives by name and `cond` on `Bool`: no operator notation (`+ - * / % ^ >>> <<< ≤ < ≥
               > == !=`) and no `if`, since the notation unfolds through `HAdd`/`instHAdd`/... before the
               kernel's GMP acceleration applies (measured about 2.5 times slower per primitive).

A further cost rule (the kernel's cost grows superlinearly in the size of one declaration, so the generated
shards check at most 500 queries per declaration) is a property of the generated shards; the generator
enforces it, not this script.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MODS = _load("check_lean_modules")

STRICT = re.compile(r"^\s*--\s*kernel-rules:\s*strict\b", re.M)
EXEMPT = re.compile(r"^\s*--\s*kernel-rules:\s*exempt\b")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec|partial|unsafe)\s+)*"
                  r"(def|abbrev|theorem|lemma|example|instance|structure|inductive|class)\b")

K1_BAD = [
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"\bdecide\s*\+\s*native\b"), "decide +native"),
    (re.compile(r"(?:\bby|;|<;>|·|^)\s*decide\b(?!\s*\+)(?![\w'])", re.M), "plain `decide` tactic (use `decide +kernel`)"),
]
K2_BAD = [
    (re.compile(r"\bNat\.blt\s+0\s+\([^()]*\+\s*1\s*\)"), "`Nat.blt 0 (x + 1)` is decided without evaluating x"),
    (re.compile(r"\bNat\.blt\s+0\s+\(\s*Nat\.succ\b"), "`Nat.blt 0 (Nat.succ x)` is decided without evaluating x"),
    (re.compile(r"\bNat\.ble\s+0\b"), "`Nat.ble 0 x` is decided without evaluating x"),
    (re.compile(r"(?<![\w.])0\s*<\s*[^=:]*\+\s*1\s*(=|$)"), "`0 < x + 1` is decided without evaluating x"),
    (re.compile(r"(?<![\w.<>≤])0\s*≤\s"), "`0 ≤ x` on naturals is decided without evaluating x"),
]
K3_BAD = [
    (re.compile(r"\bInt\b|ℤ"), "`Int` arithmetic (use sign-magnitude `Nat`)"),
    (re.compile(r"\bNat\.sqrt\b"), "`Nat.sqrt` does not reduce in the kernel"),
]
K4_BAD = [(re.compile(r"\btermination_by\b|\bdecreasing_by\b|\bpartial\s+def\b"), "well-founded recursion")]
K5_BAD = [(re.compile(r"(?<![\w.])let\s"), "`let` in a kernel-evaluated definition (pass arguments explicitly)")]
K6_BAD = [
    (re.compile(r"(?<=\s)(\+|\*|/|%|\^|>>>|<<<|≤|≥|==|!=)(?=\s)"), "operator notation (call the `Nat` primitive)"),
    (re.compile(r"(?<=\s)(<|>)(?=\s)"), "operator notation (call `Nat.blt`/`Nat.ble`)"),
    (re.compile(r"(?<=\s)-(?=\s)"), "operator notation (call `Nat.sub`)"),
    (re.compile(r"(?<![\w.])if\s"), "`if` (branch with `cond` on a `Bool`)"),
]


def certificate_files(root: Path) -> list[Path]:
    """The certificate modules: `SandierSerfaty/Certificate/` and `SandierSerfaty/CertData/`, and, when the
    optional layout file `scripts/build_roots.json` exists, every module of its certificate applications."""
    found: list[Path] = []
    for base in ("Certificate", "CertData"):
        found += sorted((root / "SandierSerfaty" / base).rglob("*.lean"))
    cfg = root / "scripts" / "build_roots.json"
    if cfg.exists():
        for app in json.loads(cfg.read_text(encoding="utf-8")).get("applications", []):
            for prefix in app.get("prefixes", []):
                base = root / Path(*prefix.split("."))
                found += sorted(base.rglob("*.lean")) if base.is_dir() else []
                if base.with_suffix(".lean").exists():
                    found.append(base.with_suffix(".lean"))
    return sorted(set(found))


def blocks(raw: str, code: str):
    """Top-level declarations: (kind, first line number, exempt?, code text of the block)."""
    raw_lines, lines = raw.splitlines(), code.splitlines()
    starts = [i for i, line in enumerate(lines) if line and not line[0].isspace()]
    starts.append(len(lines))
    for a, b in zip(starts, starts[1:]):
        match = DECL.match(lines[a])
        if not match:
            continue
        exempt = False
        j = a - 1
        while j >= 0 and not lines[j].strip():  # comments and docstrings are masked to blanks
            exempt = exempt or bool(EXEMPT.match(raw_lines[j]))
            j -= 1
        yield match.group(1), a + 1, exempt, "\n".join(lines[a:b])


def split_statement(text: str) -> tuple[str, str]:
    """(statement, proof) of a theorem/example block, split at the first top-level `:=`."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and text.startswith(":=", i):
            return text[:i], text[i + 2:]
    return text, ""


def def_body(text: str) -> tuple[str, int]:
    """The body of a definition (after its first top-level `:=`, or its first `|` alternative) and its offset;
    the patterns of match alternatives (`| n + 1, x =>`) are blanked, they are not arithmetic."""
    statement, proof = split_statement(text)
    if not proof:
        match = re.search(r"\n\s*\|", text)
        if not match:
            return "", len(text)
    text = re.sub(r"(?m)^(\s*\|)([^\n]*?)(=>)", lambda m: m.group(1) + " " * len(m.group(2)) + m.group(3), text)
    statement, proof = split_statement(text)
    if proof:
        return text, len(statement) + 2
    match = re.search(r"\n\s*\|", text)
    return text, match.start()


def check_file(root: Path, path: Path) -> list[str]:
    raw = path.read_text(encoding="utf-8")
    code = MODS.code_mask(raw)
    strict = bool(STRICT.search(raw))
    name = path.relative_to(root).as_posix()
    out: list[str] = []

    def report(line0: int, block: str, offset: int, pattern: re.Pattern, label: str, rule: str):
        for m in pattern.finditer(block, offset):
            line = line0 + block.count("\n", 0, m.start())
            out.append(f"{name}:{line}: {rule}: {label}")

    for kind, line0, exempt, text in blocks(raw, code):
        if kind in ("theorem", "lemma", "example", "instance"):
            statement, proof = split_statement(text)
            is_bool_check = bool(re.search(r"=\s*(true|false)\s*$", statement.strip()))
            for pattern, label in K1_BAD:
                report(line0, text, len(statement), pattern, label, "K1")
            if is_bool_check and re.match(r"\s*(by\s+)?rfl\b", proof):
                out.append(f"{name}:{line0}: K1: `rfl` for a Boolean check (use `decide +kernel`)")
            if re.search(r"\bdecide\s*\+\s*kernel\b", proof):
                for pattern, label in K2_BAD:
                    report(line0, statement, 0, pattern, label, "K2")
        elif kind in ("def", "abbrev") and strict and not exempt:
            text, offset = def_body(text)
            for rule, table in (("K3", K3_BAD), ("K5", K5_BAD), ("K6", K6_BAD)):
                for pattern, label in table:
                    report(line0, text, offset, pattern, label, rule)
    if strict:  # `termination_by` / `decreasing_by` usually start at column 0, outside the def block
        for pattern, label in K4_BAD:
            for number, line in enumerate(code.splitlines(), 1):
                if pattern.search(line):
                    out.append(f"{name}:{number}: K4: {label}")
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=HERE.parent)
    parser.add_argument("files", nargs="*", type=Path)
    args = parser.parse_args(argv)
    root = args.root.resolve()
    files = [f.resolve() for f in args.files] or certificate_files(root)
    if not files:
        print(f"no certificate module found under {root}; nothing was checked")
        return 1
    findings: list[str] = []
    strict = 0
    for path in files:
        strict += bool(STRICT.search(path.read_text(encoding="utf-8")))
        findings += check_file(root, path)
    for finding in findings:
        print(finding)
    print(f"{len(files)} certificate modules ({strict} strict), {len(findings)} findings")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
