"""C1366 cut provenance: which audited exterior round produced each declared cut.

Chain found by hash:
  q10-c1365-domain.json  --(cuts)-->  q10-c1366-domain.json
  cut source = q10-metric-round8-audit.json   (declared audit_sha256 of c1366)
Checks:
  P1  every declared cut of c1366 appears in the round8 audit 'cuts' list with identical
      (indices, sense, fraction_of_total);
  P2  the round8 audit has NO open cells (all cases fully closed) for the cases that
      produced cuts -- i.e. the cut is produced only from closed exterior trees;
  P3  each audit result's source_sha256 equals the hash of the domain it audited;
  P4  the transport file named by the audit exists and its own source_sha256 matches.
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


def norm(cut):
    return (tuple(sorted(cut["indices"])), cut["sense"], str(cut["fraction_of_total"]))


def main():
    out = {}
    dom = json.loads((LEAD / "q10-c1366-domain.json").read_text(encoding="utf-8"))
    declared = [norm(c["cut"]) for c in dom["cuts"]]
    out["declared_cuts_c1366"] = declared
    out["c1366_source_sha256"] = dom["source_sha256"]
    out["c1366_audit_sha256"] = dom["audit_sha256"]
    srcfile = LEAD / "q10-c1365-domain.json"
    out["c1365_sha256_matches_source"] = (sha(srcfile) == dom["source_sha256"])
    auditfile = LEAD / "q10-metric-round8-audit.json"
    out["round8_sha256_matches_audit"] = (sha(auditfile) == dom["audit_sha256"])
    a = json.loads(auditfile.read_text(encoding="utf-8"))
    out["round8_status"] = a.get("status")
    out["round8_domain_sha256"] = a.get("domain_sha256")
    out["round8_domain_matches_c1365"] = (a.get("domain_sha256") == dom["source_sha256"])
    acuts = [norm(c) for c in a.get("cuts", [])]
    out["round8_cuts"] = acuts
    out["P1_declared_subset_of_round8"] = all(c in acuts for c in declared)
    out["P1_round8_subset_of_declared"] = all(c in declared for c in acuts)
    # per-case closure
    cases = []
    for r in a.get("results", []):
        cases.append(dict(case=r.get("case"), nodes=r.get("nodes"),
                          n_excluded_leaves=len(r.get("excluded_leaves", [])),
                          n_open_cells=len(r.get("open_cells", [])),
                          source_sha256=r.get("source_sha256")))
    out["round8_cases"] = cases
    out["P2_all_cases_closed"] = all(c["n_open_cells"] == 0 for c in cases)
    # P3: each case source hash must equal the audited domain hash
    out["P3_case_sources_match_domain"] = all(c["source_sha256"] == dom["source_sha256"]
                                              for c in cases if c["source_sha256"])
    # P4 transport
    tr = LEAD / "q10-fan-transport.json"
    if tr.exists():
        t = json.loads(tr.read_text(encoding="utf-8"))
        out["transport_status"] = t.get("status")
        out["transport_n_runs"] = len(t.get("runs", []))
        out["transport_source_sha256"] = t.get("source_sha256")
        # the audit's source domain for transport: check against c1334 or earlier chain
        out["transport_source_matches_c1334"] = (
            t.get("source_sha256") == sha(LEAD / "q10-c1334-domain.json"))
        # what does each run declare?
        out["transport_run_keys"] = sorted({k for r in t.get("runs", [])[:1] for k in r})
    (HERE / "provenance-check.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    for k, v in out.items():
        if k not in ("round8_cases",):
            print(k, ":", json.dumps(v)[:300])
    print("round8_cases:", json.dumps(cases)[:600])


if __name__ == "__main__":
    main()
