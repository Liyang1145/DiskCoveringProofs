#!/usr/bin/env python3
"""Lane A session 187: static consumer-signature audit for the C450 chain.

Closes the last cheap CI-red mode that source/import/telescope audits do not
cover: a *type mismatch* at the boundary between the chain (C450ChainCompletion)
and the pre-existing consumer modules it calls.  This reads exact .lean bytes
and checks the declared signatures of the five consumer symbols against how
they are applied.  Static only -- NOT a kernel verdict and NOT a build.
"""
import hashlib, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3] / "lean" / "N11Formalization"

def read(name):
    return (ROOT / name).read_text()

def sha(b):
    return hashlib.sha256(b.encode()).hexdigest()

checks = []
def check(ok, label):
    checks.append({"ok": bool(ok), "label": label})

# --- 1. C450Source11Segment: source_of_remaining / atom_of_remaining ---
src11 = read("C450Source11Segment.lean")
check(re.search(r"theorem source_of_remaining \(hr : RemainingSourceObligation\) : SourceObligation", src11),
      "C450Source11Segment.source_of_remaining : RemainingSourceObligation -> SourceObligation")
check(re.search(r"theorem atom_of_remaining \(hr : RemainingSourceObligation\) : C450Atom", src11),
      "C450Source11Segment.atom_of_remaining : RemainingSourceObligation -> C450Atom")

# --- 2. C450NormalizedInterface: nine_of_source / ringLabels_of_source ---
norm = read("C450NormalizedInterface.lean")
check(re.search(r"theorem nine_of_source \(hs : SourceObligation\) \{c : Fin 11 . Point\} \{r : .\}\s*\n\s*\(hr : r < SourceExactRoot.sourceRadius\) \(hc : Covers c r\) :\s*\n\s*Fintype.card \(BoundaryIdx c r\) = 9", norm),
      "C450NormalizedInterface.nine_of_source : SourceObligation -> r < sourceRadius -> Covers -> card BoundaryIdx = 9")
check(re.search(r"theorem ringLabels_of_source \(hs : SourceObligation\)", norm),
      "C450NormalizedInterface.ringLabels_of_source : SourceObligation -> ... RingLabels")

# --- 3. ActualMetricClassReduction.main_of_seven_class_certificates ---
main = read("ActualMetricClassReduction.lean")
check(re.search(r"theorem main_of_seven_class_certificates\s*\n\s*\(h450 : C450Source11Segment.RemainingSourceObligation\)\s*\n\s*\(henergy : EnergyTerminalBatchB11.RemainingTerminalRadius\)\s*\n\s*\(hclasses : SevenClassExclusions\) :\s*\n\s*N11MainStatement SourceExactRoot.sourceRadius", main),
      "ActualMetricClassReduction.main_of_seven_class_certificates : h450 -> energy -> seven classes -> N11MainStatement")

# --- 4. chain usage matches: C450ChainCompletion.h450 feeds main_of_seven ---
chain = read("C450ChainCompletion.lean")
mainmod = read("C450ChainCompletionMain.lean")
check(re.search(r"C450NormalizedInterface.nine_of_source source_obligation hr hc", chain),
      "chain applies nine_of_source source_obligation hr hc (arg order/source match)")
check(re.search(r"C450NormalizedInterface.ringLabels_of_source source_obligation hr hc", chain),
      "chain applies ringLabels_of_source source_obligation hr hc")
check(re.search(r"ActualMetricClassReduction.main_of_seven_class_certificates\s*\n\s*C450ChainCompletion.h450 henergy hclasses", mainmod),
      "Main feeds C450ChainCompletion.h450 henergy hclasses in declared order")

# --- 5. RemainingSourceObligation shape is a forall over a List (not a bare Prop const) ---
s36 = read("C450Source36Segment.lean")
check(re.search(r"def RemainingSourceObligation : Prop := .* s . remainingSegs, SegmentNormalized s", src11),
      "Source11 RemainingSourceObligation := forall s in remainingSegs, SegmentNormalized s")
check(re.search(r"theorem remaining_count : remainingSegs.length = 25", src11),
      "Source11 remainingSegs.length = 25 (non-vacuous middle)")
check(re.search(r"theorem remaining_count : remainingSegs.length = 0", s36),
      "Source36 remainingSegs.length = 0 (vacuous endpoint)")

# --- 6. h450 chain consumes source16 from Mid3 and yields source11 (index math) ---
check(re.search(r"theorem source16_remaining : C450Source16Segment.RemainingSourceObligation", read("C450ChainCompletionMid3.lean")),
      "Mid3 exports source16_remaining")
check(re.search(r"theorem h450 : C450Source11Segment.RemainingSourceObligation :=", chain),
      "h450 target type is Source11 RemainingSourceObligation")

npass = sum(1 for c in checks if c["ok"])
result = {
    "audit": "c450_consumer_signatures",
    "session": 187,
    "verdict": "PASS_C450_CONSUMER_SIGNATURES" if npass == len(checks) else "FAIL",
    "checks_passed": npass,
    "checks_total": len(checks),
    "checks": checks,
    "source_hashes": {
        "C450Source11Segment.lean": sha(src11),
        "C450Source36Segment.lean": sha(s36),
        "C450NormalizedInterface.lean": sha(norm),
        "ActualMetricClassReduction.lean": sha(main),
        "C450ChainCompletion.lean": sha(chain),
        "C450ChainCompletionMain.lean": sha(mainmod),
    },
    "scope": "static signature/usage audit; NOT a kernel verdict and NOT a build",
}
out = Path(__file__).resolve().parent / "c450-consumer-signatures.json"
out.write_text(json.dumps(result, indent=2) + "\n")
print(result["verdict"], f"{npass}/{len(checks)}")
for c in checks:
    if not c["ok"]:
        print("  FAIL:", c["label"])
print("report sha256", sha(out.read_text()))
sys.exit(0 if npass == len(checks) else 1)
