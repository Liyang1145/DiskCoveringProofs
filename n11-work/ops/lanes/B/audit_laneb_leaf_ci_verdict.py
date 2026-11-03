#!/usr/bin/env python3
"""Deterministic extractor of the CI verdict for the fourteen All14 archive
leaves from the current ops/ci/LATEST.md.  Read-only: parses the (possibly
truncated) `exits` block and the `build log tail` error lines, then cross-checks
each leaf's on-disk sha256 against the recorded shape audit.

This is evidence, not kernel credit: a leaf counts only when CI shows exit 0.
"""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"
LATEST = ROOT / "n11-work" / "ops" / "ci" / "LATEST.md"
SHAPE = HERE / "audit_refine_option_shape-report.json"

CANONICAL = (38, 3432, 3490, 3517, 3550, 3564, 3569, 3578, 3738, 3781, 3825, 3854)
RESTORED = (3, 23)
ALL = RESTORED + CANONICAL


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest().upper()


def main() -> None:
    txt = LATEST.read_text(encoding="utf-8")
    head = re.search(r"# CI latest \(run (\d+)\)", txt)
    sha_line = re.search(r'"sha":\s*"([0-9a-f]+)"', txt)
    exits = dict(re.findall(r'"(N11Formalization\.[^"]+)",\s*\n\s*"(\d)"', txt))
    # errors in the build-log tail: file -> first error line
    errs: dict[str, list[str]] = {}
    for m in re.finditer(r"error: N11Formalization/(\w+)\.lean:(\d+):(\d+): ([^\n]{0,80})", txt):
        errs.setdefault(m.group(1), []).append(f"{m.group(2)}:{m.group(3)} {m.group(4).strip()}")
    shape = {Path(r["file"]).stem: r for r in json.loads(SHAPE.read_text())["leaves"]}
    rows = []
    for n in ALL:
        stem = f"EnergyRefineN{n:04d}" + ("Restored" if n in RESTORED else "")
        f = LEAN / f"{stem}.lean"
        mod = f"N11Formalization.{stem}"
        rows.append({
            "id": n,
            "module": mod,
            "on_disk_sha256": sha(f.read_bytes()) if f.exists() else None,
            "shape_sha256": shape.get(stem, {}).get("sha256"),
            "shape_decide_kernel": shape.get(stem, {}).get("decideKernel"),
            "ci_exit": exits.get(mod),
            "ci_errors": errs.get(stem, []),
        })
    print(json.dumps({
        "ci_run": head.group(1) if head else None,
        "ci_sha": sha_line.group(1) if sha_line else None,
        "exits_block_truncated": txt.count('"N11Formalization') < len(exits) + 200,
        "reds_in_summary": [k for k, v in exits.items() if v != "0"],
        "leaves": rows,
    }, indent=1))


if __name__ == "__main__":
    main()
