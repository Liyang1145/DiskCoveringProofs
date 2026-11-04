#!/usr/bin/env python3
"""Static hygiene audit of every module in lanes/B/TARGETS.txt.

Scope: token/option scan of the target .lean sources only.  This is NOT a
kernel check, NOT a build, NOT a proof; it only predicts elaboration hazards
and hard-rule violations.  Exit 0 iff every target is clean.
"""
import json, os, re, hashlib, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
LEAN = os.path.join(ROOT, "lean")
TARGETS = os.path.join(ROOT, "ops", "lanes", "B", "TARGETS.txt")
OUT = os.path.join(os.path.dirname(__file__), "audit_laneb_target_hygiene-report.json")

FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^\s*axiom\b", re.M),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
    "implemented_by": re.compile(r"\bimplemented_by\b"),
    "maxHeartbeats_0": re.compile(r"maxHeartbeats\s+0(?!\d)"),
}
OPTION = re.compile(r"set_option\s+([A-Za-z_][A-Za-z0-9_'.]*)\s+([^\n]*)")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        h.update(fh.read())
    return h.hexdigest().upper()


def scan(p, rel, module):
    src = open(p, encoding="utf-8").read()
    hits = {k: len(r.findall(src)) for k, r in FORBIDDEN.items()}
    hits = {k: v for k, v in hits.items() if v}
    opts = {}
    for name, val in OPTION.findall(src):
        opts.setdefault(name, set()).add(val.strip())
    opts = {k: sorted(v) for k, v in opts.items()}
    lines = src.splitlines()
    return {
        "module": module,
        "path": rel,
        "lines": len(lines),
        "max_line_bytes": max((len(l.encode()) for l in lines), default=0),
        "sha256": sha256(p),
        "forbidden": hits,
        "options": opts,
        "status": "CLEAN" if not hits else "FORBIDDEN",
    }


def main():
    mods = [l.strip() for l in open(TARGETS)
            if l.strip() and not l.strip().startswith("#")]
    rows, bad = [], 0
    for m in mods:
        rel = m.replace("N11Formalization.", "N11Formalization/") + ".lean"
        p = os.path.join(LEAN, rel)
        if not os.path.exists(p):
            rows.append({"module": m, "path": rel, "status": "MISSING"})
            bad += 1
            continue
        rec = scan(p, rel, m)
        if rec["forbidden"]:
            bad += 1
        rows.append(rec)
    # one-level closure: local N11Formalization imports of the targets, which
    # include the 14 All14 leaves -- the real elaboration-time risk.
    closure, seen = [], set(r["path"] for r in rows)
    for r in list(rows):
        if not os.path.exists(os.path.join(LEAN, r["path"])):
            continue
        src = open(os.path.join(LEAN, r["path"]), encoding="utf-8").read()
        for m in re.findall(r"^import\s+(N11Formalization\.[A-Za-z0-9_.]+)", src, re.M):
            rel = m.replace("N11Formalization.", "N11Formalization/") + ".lean"
            if rel in seen or not os.path.exists(os.path.join(LEAN, rel)):
                continue
            seen.add(rel)
            closure.append(scan(os.path.join(LEAN, rel), rel, m))
    closure_bad = sum(1 for r in closure if r["forbidden"])
    report = {
        "script": "audit_laneb_target_hygiene.py",
        "scope": "static token/option scan of lanes/B/TARGETS.txt sources; not a build",
        "targets": len(mods),
        "forbidden_or_missing": bad,
        "ok": bad == 0,
        "closure_modules": len(closure),
        "closure_forbidden": closure_bad,
        "rows": rows,
        "closure_rows": closure,
    }
    with open(OUT, "w") as fh:
        json.dump(report, fh, indent=1)
        fh.write("\n")
    print(json.dumps({k: report[k] for k in
                      ("targets", "forbidden_or_missing", "ok",
                       "closure_modules", "closure_forbidden")}))
    for r in rows:
        if r.get("status") != "CLEAN":
            print("  ", r["module"], r.get("status"), r.get("forbidden", ""))
    for r in closure:
        if r["forbidden"]:
            print("  closure", r["module"], r["forbidden"])
    print("report sha256", sha256(OUT))
    return 0 if bad == 0 else 1


sys.exit(main())
