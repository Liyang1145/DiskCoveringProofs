#!/usr/bin/env python3
"""Lane A session 188: static root-import safety audit for the C450 chain.

Closes the last cheap CI-red mode that the import-closure / telescope-shape /
transfer-shape / consumer-signature audits do NOT cover: what happens to the
stage-1 root *the moment the supervisor uncomments the two HARK-MISSING import
lines 1952--1953*.  Two failure modes are checked here, both purely static:

  1. the root edit itself -- exactly one commented marker per module, no
     already-live duplicate `import N11Formalization.C450ChainCompletion*`;
  2. a declaration clash -- uncommenting introduces the chain's namespaces and
     top-level names into the root scope for the first time, so no other
     module in the tree may already declare them.

This reads exact .lean bytes and scans every module in N11Formalization.  It is
STATIC ONLY -- NOT a kernel verdict and NOT a build.
"""
import hashlib, json, re, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean"
ROOT_DIR = LEAN / "N11Formalization"
ROOT = LEAN / "N11Formalization.lean"

CHAIN_MODULES = [
    "C450ChainCompletionEndpoint",
    "C450ChainCompletionTail",
    "C450ChainCompletionMid1",
    "C450ChainCompletionMid2",
    "C450ChainCompletionMid3",
    "C450ChainCompletion",
    "C450ChainCompletionMain",
    "C450ChainCompletionAudit",
]
NAMESPACES = [
    "N11Formalization.C450ChainCompletionEndpoint",
    "N11Formalization.C450ChainCompletionTail",
    "N11Formalization.C450ChainCompletionMid1",
    "N11Formalization.C450ChainCompletionMid2",
    "N11Formalization.C450ChainCompletionMid3",
    "N11Formalization.C450ChainCompletion",
    "N11Formalization.C450ChainCompletionMain",
    "N11Formalization.C450ChainCompletionAudit",
]
# Fully-qualified top-level names the chain exports into the root scope.
EXPORTED = [
    "N11Formalization.C450ChainCompletion.h450",
    "N11Formalization.C450ChainCompletion.source_obligation",
    "N11Formalization.C450ChainCompletion.c450_atom",
    "N11Formalization.C450ChainCompletion.chain_step_count",
]
MARKER = "-- HARK-MISSING (not in public assets; lane A reconstructs): import "
IMPORTS = [
    "N11Formalization.C450ChainCompletion",
    "N11Formalization.C450ChainCompletionMain",
]

def sha(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()

checks = []
def check(ok, label):
    checks.append({"ok": bool(ok), "label": label})

root = ROOT.read_text(encoding="utf-8")

# --- 1. the root edit is exactly two commented markers, no live duplicate ---
for imp in IMPORTS:
    commented = f"{MARKER}{imp}"
    live = f"import {imp}"
    check(len(re.findall(rf"(?m)^{re.escape(commented)}\s*$", root)) == 1, f"exactly one commented marker for {imp}")
    # a live import must not already exist (it would double-import on uncomment)
    live_hits = len(re.findall(rf"(?m)^{re.escape(live)}\s*$", root))
    check(live_hits == 0, f"no already-live `import {imp}` in the root")
    check(live not in root.replace(commented, ""),
          f"the only occurrence of `import {imp}` is the commented marker")

# --- 2. uncommenting introduces no name/namespace clash ---
ns_pat = {ns: re.compile(rf"(?m)^\s*namespace {re.escape(ns)}\s*$") for ns in NAMESPACES}
# top-level declaration of a short name inside a given namespace (declared on its
# own line, preceded by an indented `namespace` line above in the same file).
exported_names = {e.rsplit(".", 1)[1] for e in EXPORTED}
name_pat = re.compile(
    r"(?m)^(?:theorem|lemma|def|abbrev|noncomputable def|instance|structure)\s+"
    r"(" + "|".join(sorted(exported_names)) + r")\b"
)

ns_owners: dict[str, list[str]] = {ns: [] for ns in NAMESPACES}
name_owners: dict[str, list[str]] = {n: [] for n in exported_names}
scanned = 0
for path in sorted(ROOT_DIR.glob("*.lean")):
    scanned += 1
    text = path.read_text(encoding="utf-8")
    stem = path.stem
    for ns, pat in ns_pat.items():
        if pat.search(text):
            ns_owners[ns].append(stem)
    # only count exported-name declarations that sit inside a chain namespace
    if any(ns in NAMESPACES and pat.search(text) for ns, pat in ns_pat.items()):
        for m in name_pat.finditer(text):
            name_owners[m.group(1)].append(stem)

allowed = set(CHAIN_MODULES)
for ns, owners in ns_owners.items():
    outside = [o for o in owners if o not in allowed]
    check(bool(owners) and not outside,
          f"namespace {ns} declared only in the chain modules (owners={owners})")
for name in sorted(name_owners):
    owners = name_owners[name]
    outside = [o for o in owners if o not in allowed]
    check(len(owners) == 1 and not outside,
          f"exported name `{name}` declared exactly once, in the chain (owners={owners})")

# --- 3. the chain modules themselves carry no forbidden token ---
forbidden = ("sorry", "admit", "axiom ", "native_decide", "ofReduceBool",
             "implemented_by", "maxHeartbeats 0")
for mod in CHAIN_MODULES:
    text = (ROOT_DIR / f"{mod}.lean").read_text(encoding="utf-8")
    hits = [t for t in forbidden if t in text]
    check(not hits, f"{mod}.lean has no forbidden token ({hits})")

ok = all(c["ok"] for c in checks)
report = {
    "audit": "c450_root_import_safety",
    "session": 188,
    "verdict": "PASS_C450_ROOT_IMPORT_SAFETY" if ok else "FAIL_C450_ROOT_IMPORT_SAFETY",
    "checks_passed": sum(c["ok"] for c in checks),
    "checks_total": len(checks),
    "checks": checks,
    "modules_scanned": scanned,
    "source_hashes": {
        "N11Formalization.lean": sha(root),
        **{f"{m}.lean": sha((ROOT_DIR / f"{m}.lean").read_text(encoding="utf-8")) for m in CHAIN_MODULES},
    },
    "scope": "static root-import / name-clash audit; NOT a kernel verdict and NOT a build",
}
out = HERE / "c450-root-import-safety.json"
out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
print(f"modules scanned: {scanned}")
for c in checks:
    print(("PASS" if c["ok"] else "FAIL") + " " + c["label"])
print(f"\n{report['verdict']}: {report['checks_passed']}/{report['checks_total']} checks")
print("report sha256:", sha(json.dumps(report, indent=2) + "\n"))
sys.exit(0 if ok else 1)
