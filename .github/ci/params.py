#!/usr/bin/env python3
"""Resolve the track parameters of a CI build from the pinned contract.

Environment:
  TRACK        track slug from .contract/challenges.json (default upper-riscv)
  SOURCE_ROOT  folder of this repository holding the candidate root
               (default: the track's submission_root, e.g. formal/Submissions/UpperRiscv)

Prints `key=value` lines for $GITHUB_OUTPUT.
"""
from __future__ import annotations

import hashlib
import json
import os
import sys
from pathlib import Path

CONTRACT = Path(".contract")
CACHE_VERSION = "v1"  # bump to invalidate every warm .lake


def digest(paths: list[Path]) -> str:
    h = hashlib.sha256()
    for p in paths:
        h.update(str(p).encode() + b"\0")
        h.update(p.read_bytes())
        h.update(b"\0")
    return h.hexdigest()[:16]


def main() -> int:
    cfg = json.loads((CONTRACT / "challenges.json").read_text())
    slug = os.environ.get("TRACK") or "upper-riscv"
    tracks = {t["slug"]: t for t in cfg["tracks"]}
    if slug not in tracks:
        print(f"unknown track {slug!r}; known: {sorted(tracks)}", file=sys.stderr)
        return 1
    t = tracks[slug]
    lean_root = cfg.get("lean_root", "formal")
    source_root = (os.environ.get("SOURCE_ROOT") or "").strip().strip("/") or t["submission_root"]
    src = Path(source_root)
    if not src.is_dir():
        print(f"source root {source_root} does not exist in this checkout", file=sys.stderr)
        return 1
    claim_file = src / "claim.txt"
    claim = claim_file.read_text().strip() if claim_file.is_file() else ""

    comparator = json.loads((CONTRACT / t["comparator_config"]).read_text())
    names = list(comparator.get("definition_names", [])) + list(comparator.get("theorem_names", []))

    formal = CONTRACT / lean_root
    toolchain_files = [formal / "lean-toolchain", formal / "lake-manifest.json", formal / "lakefile.lean"]
    contract_files = sorted(
        p for p in [formal / "OptimalOTS.lean", *(formal / "OptimalOTS").rglob("*.lean")]
        # rendered challenge stubs are generated, never part of the warm build
        if p.parent.name != "Challenge"
    )
    runner_os = os.environ.get("RUNNER_OS", "Linux")
    prefix = f"lake-{CACHE_VERSION}-{runner_os}-{digest(toolchain_files)}-"
    key = prefix + digest(contract_files)

    out = {
        "track": slug,
        "lean_root": lean_root,
        "submission_root": t["submission_root"],
        "source_root": source_root,
        "module_prefix": t["module_prefix"],
        "solution_module": t["solution_module"],
        "challenge_module": t["challenge_module"],
        "challenge_template": t["challenge_template"],
        "comparator_config": t["comparator_config"],
        "declarations": " ".join(names),
        "claim": claim,
        "lake_key": key,
        "lake_key_prefix": prefix,
    }
    for k, v in out.items():
        print(f"{k}={v}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
