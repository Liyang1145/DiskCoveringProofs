#!/usr/bin/env python3
"""Lane B: root-cause the lane-B census reds from CI run 41706645384.

Run 41706645384 (head bd5573e5) tested the *old* block-form
EnergyTerminalResidualCensusC01-C04.  The full job log (job 126192939954,
602 MB, downloaded to /tmp/j4170.zip) shows C01 alone failing 27 times at
703-766 s each with `(kernel) deep recursion detected` and `(deterministic)
timeout at whnf`.  This script re-extracts those facts from the log when it is
present, records the old source form that produced them, and reports the
current (post-a714ed6b) per-index rewrite state.  Scope: CI log + source
bytes only -- no Lean build, no kernel credit.
"""
import hashlib
import json
import os
import re

LOG = os.environ.get("CENSUS_CI_LOG", "/tmp/j4170.zip")
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, "..", "..", "lean", "N11Formalization"))

RECORDED = {
    "run_id": 41706645384,
    "job_id": 126192939954,
    "ci_head": "bd5573e58d23d69cbdb4a154c9c382e7956962b4",
    "old_c01_blob": "86f707fd524cfe71f654036aaae0236f4dc4b619",
    "module": "N11Formalization.EnergyTerminalResidualCensusC01",
    "first_kernel_deep_recursion": "EnergyTerminalResidualCensusC01.lean:16:56",
    "kernel_deep_recursion_count": 270,
    "whnf_timeout_count": 351,
    "build_attempts": 27,
    "build_seconds_min": 703,
    "build_seconds_max": 766,
}

OLD_SOURCE_SNIPPET = [
    "theorem mem_iff_block00 (n : Fin 5011)",
    "    (hlo : 0 \u2264 n.val) (hhi : n.val < 100) :",
    "    n \u2208 residualIDs \u2194 n \u2208 EnergyTerminalBatchB13.residualIDs := by",
    "  rcases n with \u27e8k, hk\u27e9",
    "  interval_cases k <;>",
    "    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel +revert",
]


def scan_log(path):
    if not os.path.exists(path):
        return None
    pat_dr = re.compile(r"(EnergyTerminalResidualCensusC0[1-4])\\.lean:(\\d+):(\\d+): \\(kernel\\) deep recursion")
    pat_to = re.compile(r"(EnergyTerminalResidualCensusC0[1-4])\\.lean:(\\d+):0: \\(deterministic\\) timeout at `whnf`")
    pat_build = re.compile(r"Building (N11Formalization\\.EnergyTerminalResidualCensusC01) \\((\\d+)s\\)")
    dr, to, secs = {}, {}, []
    with open(path, "r", errors="replace") as fh:
        for line in fh:
            m = pat_dr.search(line)
            if m:
                dr[m.group(1)] = dr.get(m.group(1), 0) + 1
            m = pat_to.search(line)
            if m:
                to[m.group(1)] = to.get(m.group(1), 0) + 1
            m = pat_build.search(line)
            if m:
                secs.append(int(m.group(2)))
    return {"deep_recursion": dr, "whnf_timeout": to, "build_seconds": secs}


def current_state():
    out = {}
    for tag in ("C01", "C02", "C03", "C04"):
        p = os.path.join(LEAN, "EnergyTerminalResidualCensus%s.lean" % tag)
        if not os.path.exists(p):
            out[tag] = {"present": False}
            continue
        data = open(p, "rb").read()
        txt = data.decode("utf-8", "replace")
        out[tag] = {
            "present": True,
            "sha256": hashlib.sha256(data).hexdigest(),
            "decide_kernel_count": txt.count("decide +kernel"),
            "per_index_theorems": len(re.findall(r"theorem mem_iff_id_\\d+", txt)),
            "block_interval_cases": txt.count("interval_cases k"),
        }
    return out


def main():
    log = scan_log(LOG)
    report = {
        "scope": "CI job log + source bytes; not a build, not kernel credit",
        "recorded_facts": RECORDED,
        "old_source_form": OLD_SOURCE_SNIPPET,
        "log_recheck": log,
        "current_source_state": current_state(),
    }
    out = os.path.join(HERE, "audit_census_c01_ci_rootcause-report.json")
    with open(out, "w") as fh:
        json.dump(report, fh, indent=1, sort_keys=True)
    print("log present:", log is not None)
    if log:
        print("deep recursion by module:", log["deep_recursion"])
        print("whnf timeout by module:", log["whnf_timeout"])
        bs = log["build_seconds"]
        print("build seconds range:", (min(bs), max(bs)) if bs else None)
    for tag, st in report["current_source_state"].items():
        if st.get("present"):
            print(tag, "decide+kernel=", st["decide_kernel_count"], "per_index=", st["per_index_theorems"], "interval_cases=", st["block_interval_cases"])
    print("wrote", out)


if __name__ == "__main__":
    main()
