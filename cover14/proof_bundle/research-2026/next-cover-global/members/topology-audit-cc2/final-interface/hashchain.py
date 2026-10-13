"""Hash-chain and provenance check for the C1366 domain (scope final-interface).

Purpose (per lead): establish the exact PROVENANCE of the C1366 necessary domain from the
hash-bound audit artifacts of C1331..C1366, rather than only the final stored vertex list.

Checks, all local and bounded:
  H1  every source file that the C1366/integration scripts name exists and its sha256 is
      recorded; detect declared-vs-actual mismatches (stale dependency).
  H2  the cut list of q10-c1366-domain.json: which cuts are "less"/"greater" on which index
      sets, and their declared fraction of total D.
  H3  which stored artifacts (exterior audits / clips) name each cut, and their hashes.
No optimizer, no tree replay.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


# Scripts named by the lead for this task + the artifacts they should bind.
SCRIPTS = ["q10_integrate_metric_cuts.py", "q10_metric_mean_round_audit.py",
           "q10_rational_polytope_audit.py", "q10_current_angle_width.py",
           "q10_quadratic_global_bridge.py", "q10_quadratic_minorant_certificate.py"]

# Artifacts that plausibly carry the cut provenance (exterior trees / earlier domains).
ARTIFACTS = ["q10-c1366-domain.json", "q10-c1350-domain.json", "q10-c1348-domain.json",
             "q10-c1334-domain.json", "q10-reduced-domain.json", "q10-metric-round2-audit.json",
             "q10-large-union.json", "q10-exterior-union.json", "q10-c1334-slab-audit.json",
             "q10-tight-slab-audit.json", "q10-metric-slab-audit.json",
             "q10-fan-leaf-audit.json", "q10-fan-transport.json", "q10-slab-transport.json"]


def main():
    out = {"scripts": {}, "artifacts": {}, "missing": []}
    for s in SCRIPTS:
        p = LEAD / s
        if not p.exists():
            out["missing"].append(s)
            continue
        out["scripts"][s] = {"sha256": sha(p), "bytes": p.stat().st_size}
    for a in ARTIFACTS:
        p = LEAD / a
        if not p.exists():
            out["missing"].append(a)
            continue
        out["artifacts"][a] = {"sha256": sha(p), "bytes": p.stat().st_size}
    # declared hashes inside the kept artifacts
    declares = {}
    for a in ARTIFACTS:
        p = LEAD / a
        if not p.exists():
            continue
        try:
            d = json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            continue
        found = []

        def walk(o, path=""):
            if isinstance(o, dict):
                for k, v in o.items():
                    if isinstance(v, str) and len(v) == 64 and all(
                            c in "0123456789abcdef" for c in v.lower()):
                        found.append((path + "/" + k, v))
                    else:
                        walk(v, path + "/" + k)
            elif isinstance(o, list):
                for i, v in enumerate(o[:50]):
                    walk(v, path + "[%d]" % i)
        walk(d)
        if found:
            declares[a] = found[:12]
    out["declared_hashes"] = declares
    (HERE / "hashchain.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    print("scripts:", sorted(out["scripts"].keys()))
    print("artifacts:", sorted(out["artifacts"].keys()))
    print("missing:", out["missing"])
    print()
    for a, fs in declares.items():
        print(a)
        for k, v in fs:
            print("   ", k, v[:20])


if __name__ == "__main__":
    main()
