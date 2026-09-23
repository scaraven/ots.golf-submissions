#!/usr/bin/env python3
"""Append a Markdown digest of a Lake/Lean log to $GITHUB_STEP_SUMMARY (or stdout).

    summarize_log.py LOG TITLE [--outcome OUTCOME] [--seconds N] [--mem MEMLOG]

Every line containing `error:` is shown with 2 lines before and 20 after (overlapping
blocks are merged), followed by the log tail. The summary is capped well below GitHub's
1 MiB per-step limit; the full log is uploaded as an artifact.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

BEFORE, AFTER = 2, 20
CAP = 800_000
FENCE = "````"


def ranges(hits: list[int], n: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    for i in hits:
        lo, hi = max(0, i - BEFORE), min(n, i + AFTER + 1)
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], hi))
        else:
            out.append((lo, hi))
    return out


def peak_from_time(lines: list[str]) -> str | None:
    for line in lines:
        m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", line)
        if m:
            return f"{int(m.group(1)) / 1024 / 1024:.2f} GiB (largest single process, /usr/bin/time)"
    return None


def peak_from_memlog(path: Path) -> str | None:
    if not path.is_file():
        return None
    mem = swap = 0
    for line in path.read_text(errors="replace").splitlines():
        m = re.search(r"mem_used=(\d+)", line)
        s = re.search(r"swap_used=(\d+)", line)
        if m:
            mem = max(mem, int(m.group(1)))
        if s:
            swap = max(swap, int(s.group(1)))
    return f"{mem / 1024:.2f} GiB RAM + {swap / 1024:.2f} GiB swap (whole runner, 30 s samples)"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("log", type=Path)
    ap.add_argument("title")
    ap.add_argument("--outcome", default="")
    ap.add_argument("--seconds", default="")
    ap.add_argument("--mem", type=Path)
    a = ap.parse_args()

    text = a.log.read_text(errors="replace") if a.log.is_file() else ""
    lines = text.splitlines()
    err_idx = [i for i, l in enumerate(lines) if "error:" in l]
    warn_count = sum(1 for l in lines if "warning:" in l)

    md: list[str] = [f"## {a.title}", ""]
    if a.outcome:
        md.append(f"- outcome: **{a.outcome}**")
    if a.seconds:
        s = int(a.seconds)
        md.append(f"- wall time: {s // 60} min {s % 60} s")
    peak = peak_from_time(lines)
    if peak:
        md.append(f"- peak RSS: {peak}")
    if a.mem:
        pm = peak_from_memlog(a.mem)
        if pm:
            md.append(f"- peak memory: {pm}")
    md.append(f"- `error:` lines: {len(err_idx)}; `warning:` lines: {warn_count}; log lines: {len(lines)}")
    md.append("")

    if err_idx:
        md += ["### Errors (2 lines before, 20 after)", "", FENCE + "text"]
        body: list[str] = []
        for lo, hi in ranges(err_idx, len(lines)):
            body.append(f"--- log lines {lo + 1}-{hi} ---")
            body += lines[lo:hi]
        blob = "\n".join(body)
        if len(blob) > CAP:
            blob = blob[:CAP] + "\n[... truncated; see the build-logs artifact]"
        md += [blob, FENCE, ""]

    md += ["### Log tail", "", FENCE + "text", *lines[-25:], FENCE, ""]
    out = "\n".join(md) + "\n"
    target = os.environ.get("GITHUB_STEP_SUMMARY")
    if target:
        with open(target, "a", encoding="utf-8") as f:
            f.write(out)
    # Also echo the error blocks into the job log for quick reading.
    sys.stdout.write(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
