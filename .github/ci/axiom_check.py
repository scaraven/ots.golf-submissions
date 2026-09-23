#!/usr/bin/env python3
"""Statement sanity check and axiom report for the exported declarations.

    axiom_check.py gen   TRACK CLAIM OUT.lean     # write the Lean check file
    axiom_check.py check TRACK LOG                # parse `lake env lean` output, exit 1 on a bad axiom

`gen` renders the track's challenge stub with CLAIM, replaces its imports by the solution
module, turns every `theorem NAME : T := sorry` into `example : T := NAME` and every
`def NAME : T := sorry` into `#check (NAME : T)` (so the
submitted declaration must elaborate against the stub's statement, up to definitional
equality; comparator's exact comparison is stricter), then appends `#print axioms` for every
declaration comparator checks. Run from the repository root (reads .contract/).
"""
from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path

CONTRACT = Path(".contract")
DECL_RE = re.compile(
    r"(?:(?:noncomputable|private|protected)\s+)*(theorem|lemma|def|abbrev)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)\s*:(.*?):=\s*sorry",
    re.S,
)


def load(slug: str) -> tuple[dict, dict, dict]:
    cfg = json.loads((CONTRACT / "challenges.json").read_text())
    t = next(t for t in cfg["tracks"] if t["slug"] == slug)
    comp = json.loads((CONTRACT / t["comparator_config"]).read_text())
    return cfg, t, comp


def names(comp: dict) -> list[str]:
    return list(comp.get("definition_names", [])) + list(comp.get("theorem_names", []))


def gen(slug: str, claim: str, out: Path) -> int:
    _, t, comp = load(slug)
    template = (CONTRACT / t["challenge_template"]).read_text()
    text = template.replace("{{CLAIM}}", claim)
    text = re.sub(r"/--.*?-/", "", text, flags=re.S)          # doc comments cannot precede `example`
    body = "\n".join(l for l in text.splitlines() if not l.startswith("import "))
    def repl(m: re.Match) -> str:
        kind, name, stmt = m.group(1), m.group(2), m.group(3).strip()
        if kind in ("theorem", "lemma"):
            return f"example : {stmt} := {name}"
        # a data definition: an `example` would be compiled, so only check its type
        return f"#check ({name} : {stmt})"

    body, n = DECL_RE.subn(repl, body)
    if n == 0:
        print("warning: no `:= sorry` declaration found in the stub", file=sys.stderr)
    lines = [f"import {t['solution_module']}", "",
             "/-! CI check: the stub's statements, instantiated with the submission's claim. -/",
             body.strip(), ""]
    lines += [f"#print axioms {n}" for n in names(comp)]
    out.write_text("\n".join(lines) + "\n")
    print(out.read_text())
    return 0


def check(slug: str, log: Path) -> int:
    _, _, comp = load(slug)
    permitted = set(comp.get("permitted_axioms", []))
    text = log.read_text(errors="replace") if log.is_file() else ""
    found: dict[str, list[str]] = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        found[m.group(1)] = [a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        found[m.group(1)] = []
    md = ["## Axioms", "", f"permitted: `{', '.join(sorted(permitted))}`", "",
          "| declaration | axioms | ok |", "|---|---|---|"]
    ok = True
    for n in names(comp):
        if n not in found:
            ok = False
            md.append(f"| `{n}` | *(not printed)* | NO |")
            continue
        bad = [a for a in found[n] if a not in permitted]
        ok &= not bad
        md.append(f"| `{n}` | `{', '.join(found[n]) or '(none)'}` | {'yes' if not bad else 'NO: ' + ', '.join(bad)} |")
    md += ["", "Raw output:", "", "````text", text.strip()[-20000:], "````", ""]
    out = "\n".join(md) + "\n"
    target = os.environ.get("GITHUB_STEP_SUMMARY")
    if target:
        with open(target, "a", encoding="utf-8") as f:
            f.write(out)
    print(out)
    return 0 if ok else 1


def main(argv: list[str]) -> int:
    if len(argv) == 4 and argv[0] == "gen":
        return gen(argv[1], argv[2], Path(argv[3]))
    if len(argv) == 3 and argv[0] == "check":
        return check(argv[1], Path(argv[2]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
