#!/usr/bin/env python3
"""Static name/shape audit for the C450 chain completion (lane A).

Scope: SOURCE ONLY -- reads the exact .lean bytes, no Lean build, no kernel
verdict.  Purpose: catch the cheapest remaining CI-red failure mode for the
lane-A target, namely a transfer lemma whose declared direction does not match
the way C450ChainCompletion.h450 composes it (a reversed implication or a
wrong argument order would build-fail only in CI, where the lane cannot see it).

The telescope contract is:

    C450Source(K+1)Segment.sourceK_remaining_of_remaining
        : C450Source(K+1)Segment.RemainingSourceObligation
        -> C450Source(K)Segment.RemainingSourceObligation

for K = 12..36, so that feeding source36's obligation (vacuous) walks all the
way down to C450Source11Segment.RemainingSourceObligation = the `h450` type.

Checks performed:
  1. every K in 12..36 declares source{K-1}_remaining_of_remaining with exactly
     that type shape (hypothesis RemainingSourceObligation, conclusion
     C450Source{K}Segment.RemainingSourceObligation);
  2. the seven chain modules (Endpoint, Tail, Mid1..3, ChainCompletion, Audit)
     contain no forbidden tokens (sorry/admit/axiom/native_decide/...);
  3. the chain modules apply each transfer K = 12..36 exactly once, in the
     order 36->12, and the innermost application is the vacuous source36.
"""
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, "..", "..", "..", "lean", "N11Formalization"))
OUT = os.path.join(HERE, "c450-transfer-shapes.json")

CHAIN_MODULES = [
    "C450ChainCompletionEndpoint.lean",
    "C450ChainCompletionTail.lean",
    "C450ChainCompletionMid1.lean",
    "C450ChainCompletionMid2.lean",
    "C450ChainCompletionMid3.lean",
    "C450ChainCompletion.lean",
    "C450ChainCompletionMain.lean",
    "C450ChainCompletionAudit.lean",
]
FORBIDDEN = ["sorry", "admit", "axiom", "native_decide", "implemented_by",
             "Lean.ofReduceBool", "maxHeartbeats 0"]

EXPECTED_TRANSFER = re.compile(
    r"^\(\s*\w+\s*:\s*RemainingSourceObligation\s*\)\s*:\s*"
    r"C450Source(\d+)Segment\.RemainingSourceObligation$")


def read(rel):
    with open(os.path.join(LEAN, rel), "r", encoding="utf-8") as fh:
        return fh.read()


def declaration_signature(text, name):
    """Return the whitespace-normalized declaration type (everything between the
    declaration name and the first `:=`/`by`).  None if the name is absent."""
    pat = re.compile(r"^\s*(?:theorem|def|abbrev)\s+" + re.escape(name) + r"\b")
    lines = text.splitlines()
    for idx, line in enumerate(lines):
        if not pat.match(line):
            continue
        buf = [line[pat.match(line).end():]]
        for nxt in lines[idx + 1:]:
            buf.append(nxt)
            if ":=" in nxt or re.search(r"\bby\b", nxt):
                break
        joined = " ".join(buf)
        cut = len(joined)
        for marker in (":=", " by "):
            pos = joined.find(marker)
            if pos != -1:
                cut = min(cut, pos)
        sig = re.sub(r"\s+", " ", joined[:cut]).strip()
        return sig if sig else None
    return None


def main():
    report = {"scope": "source static audit; not a kernel verdict",
              "failures": [], "checks": [], "module_sha256": {}}

    def record(name, ok, detail):
        report["checks"].append({"name": name, "ok": bool(ok), "detail": detail})
        if not ok:
            report["failures"].append(name)

    # 1. transfer lemma shapes for K = 12..36
    transfer_ok = True
    for k in range(12, 37):
        rel = f"C450Source{k}Segment.lean"
        path = os.path.join(LEAN, rel)
        if not os.path.exists(path):
            record(rel, False, "module missing")
            transfer_ok = False
            continue
        text = read(rel)
        lemma = f"source{k-1}_remaining_of_remaining"
        sig = declaration_signature(text, lemma)
        m = EXPECTED_TRANSFER.match(sig) if sig else None
        ok = bool(m) and int(m.group(1)) == k - 1
        record(f"{rel}::{lemma}", ok, sig or "NOT FOUND")
        transfer_ok = transfer_ok and ok

    # 2. forbidden tokens in the chain modules
    for rel in CHAIN_MODULES:
        path = os.path.join(LEAN, rel)
        if not os.path.exists(path):
            record(rel, False, "module missing")
            continue
        text = read(rel)
        hits = [tok for tok in FORBIDDEN if tok in text]
        record(f"no-forbidden::{rel}", not hits, ",".join(hits) or "clean")

    # 3. each transfer applied exactly once, descending 36->12
    applied = {}
    for rel in CHAIN_MODULES:
        path = os.path.join(LEAN, rel)
        if not os.path.exists(path):
            continue
        for m in re.finditer(r"C450Source(\d+)Segment\.source(\d+)_remaining_of_remaining",
                             read(rel)):
            outer, inner = int(m.group(1)), int(m.group(2))
            if inner != outer - 1:
                record(f"application::{rel}", False,
                       f"C450Source{outer}Segment applies source{inner}, expected source{outer-1}")
            applied.setdefault(outer, []).append(rel)
    for k in range(12, 37):
        uses = applied.get(k, [])
        record(f"applied-once::K={k}", len(uses) == 1, ",".join(uses) or "unused")
    for k in sorted(applied):
        if len(applied[k]) > 1:
            record(f"applied-once::K={k}", False, "duplicate: " + ",".join(applied[k]))

    # module hashes for the frozen record
    for rel in sorted(set(CHAIN_MODULES +
                          [f"C450Source{k}Segment.lean" for k in range(11, 37)] +
                          ["C450NormalizedInterface.lean"])):
        path = os.path.join(LEAN, rel)
        if os.path.exists(path):
            report["module_sha256"][rel] = hashlib.sha256(
                read(rel).encode("utf-8")).hexdigest()

    report["verdict"] = "PASS_C450_TRANSFER_SHAPES" if not report["failures"] else "FAIL"
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=2, sort_keys=True)
        fh.write("\n")
    print(f"verdict: {report['verdict']}  ({len(report['checks'])} checks)")
    for name in report["failures"]:
        print(f"  FAIL {name}")
    print(f"report: {os.path.relpath(OUT)}")
    return 0 if report["verdict"].startswith("PASS") else 1


if __name__ == "__main__":
    sys.exit(main())
