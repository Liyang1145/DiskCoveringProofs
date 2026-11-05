#!/usr/bin/env python3
"""Lane-A q0 CI red census from the FULL n11-lean-build job log.

Why: ops/ci/LATEST.md embeds only the first 6000 chars of summary.json, and
lane A's targets build LAST, so LATEST.md never shows lane-A exits.  This
script parses a downloaded full job log (read-only) and reports the lane-A
q0 `=== EXIT` codes plus the root-cause `error:` lines per q0 file.  It is an
observation of CI output, NOT a kernel verdict.

Usage: python3 audit_q0_ci_red_census.py --offline LOG --out OUT.json
"""
from __future__ import annotations
import argparse, json, re
from pathlib import Path

EXIT = re.compile(r"=== EXIT (\S+) (\d+)")
ERR = re.compile(r"error: N11Formalization/(\S+\.lean):(\d+):(\d+): (.*)")
Q0 = re.compile(r"SevenClassQ0Deg3")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--offline", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    exits, errs = {}, {}
    for line in Path(a.offline).read_text("utf-8", errors="replace").splitlines():
        m = EXIT.search(line)
        if m and Q0.search(m.group(1)):
            exits[m.group(1)] = int(m.group(2))
        e = ERR.search(line)
        if e and Q0.search(e.group(1)):
            key = f"{e.group(1)}:{e.group(2)}:{e.group(3)}"
            errs.setdefault(key, e.group(4)[:120])
    red = sorted(t for t, rc in exits.items() if rc != 0)
    rep = {
        "scope": "full n11-lean-build job log (read-only); observation of CI output, NOT a kernel verdict",
        "q0_targets_seen": len(exits),
        "q0_red": red,
        "q0_red_count": len(red),
        "root_cause_errors": errs,
        "distinct_root_causes": sorted(set(errs.values())),
    }
    Path(a.out).write_text(json.dumps(rep, indent=1) + "\n", encoding="utf-8")
    print(json.dumps({"q0_red_count": rep["q0_red_count"],
                      "q0_red": red,
                      "distinct_root_causes": rep["distinct_root_causes"]}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
