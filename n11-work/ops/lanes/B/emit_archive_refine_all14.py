#!/usr/bin/env python3
"""Audit and consume the fourteen structurally complete archive refinements.

The twelve canonical modules below differ from the archived sources only by
removal of one `set_option maxHeartbeats 0`; ids 3 and 23 already have fresh
`...Restored` modules.  This script re-audits those byte relations and emits a
deterministic consumer.  It never edits a source or changes an ID.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"
BRANCH = "origin/ci/n11-build"
ARCHIVE = "ci-n11/drafts/energy/N11Formalization"
CANONICAL_IDS = (38, 3432, 3490, 3517, 3550, 3564, 3569, 3578, 3738, 3781, 3825, 3854)
RESTORED_IDS = (3, 23)
ALL_IDS = RESTORED_IDS + CANONICAL_IDS
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def audit_source(node: int) -> dict[str, str | int]:
    path = f"{ARCHIVE}/EnergyRefineN{node:04d}.lean"
    archive = subprocess.check_output(["git", "show", f"{BRANCH}:{path}"], cwd=ROOT)
    directive = b"set_option maxHeartbeats 0\n"
    if archive.count(directive) != 1:
        raise SystemExit(f"{path}: expected exactly one unbounded heartbeat")
    expected = archive.replace(directive, b"")
    current = (LEAN / f"EnergyRefineN{node:04d}.lean").read_bytes()
    if current != expected:
        raise SystemExit(f"node {node}: current bytes differ from archive minus directive")
    text = current.decode("utf-8")
    if FORBIDDEN.search(text):
        raise SystemExit(f"node {node}: forbidden declaration remains")
    if f"namespace N11Formalization.EnergyRefineN{node:04d}" not in text:
        raise SystemExit(f"node {node}: unexpected namespace")
    if f"def newIDs : Finset (Fin 5011) := {{{node}}}" not in text:
        raise SystemExit(f"node {node}: unexpected newIDs")
    return {
        "id": node,
        "archive_sha256": digest(archive),
        "current_sha256": digest(current),
        "bytes": len(current),
    }


def module(node: int) -> str:
    suffix = "Restored" if node in RESTORED_IDS else ""
    return f"EnergyRefineN{node:04d}{suffix}"


def namespace_module(node: int) -> str:
    """The restored source keeps its original namespace, despite the file suffix."""
    return f"EnergyRefineN{node:04d}"


def emit(rows: list[dict[str, str | int]]) -> str:
    imports = "\n".join(
        f"import N11Formalization.{module(node)}" for node in ALL_IDS)
    names = ", ".join(str(node) for node in ALL_IDS)
    helpers = []
    for node in ALL_IDS:
        ns = namespace_module(node)
        helpers.append(f"""theorem certificate{node} :
    EnergyTerminalBatchB13.ResidualRadiusCertificate {node} := by
  constructor
  intro y hy0 hy1 hc C Z r hf
  exact ({ns}.new_radius {node} (by simp [{ns}.newIDs])
    y hy0 hy1 hc C Z r hf).le
""")
    branches = "\n".join(
        f"  · exact certificate{node}" for node in ALL_IDS)
    cases = " | ".join("rfl" for _ in ALL_IDS)
    return f"""import N11Formalization.EnergyTerminalBatchB13ResidualCertificates
import N11Formalization.LaneBResidual346Bridge
{imports}

/-! Discharge the fourteen ids having structurally complete archive refinements.
The twelve canonical modules are byte-identical to their archived source except
for removal of one unbounded heartbeat directive; ids 3 and 23 use fresh
restored modules.  The remaining interface is exact at 332 ids.  No theorem here
proves a residual packet or the seven class exclusions. -/
set_option autoImplicit false
namespace N11Formalization.LaneBArchiveRefineAll14
open N11Formalization SourceChartIsometry ResumeNetwork
noncomputable section

def archiveIDs : Finset (Fin 5011) := {{{names}}}

{''.join(helpers)}
theorem certificateOf (n : Fin 5011) (hn : n ∈ archiveIDs) :
    EnergyTerminalBatchB13.ResidualRadiusCertificate n := by
  simp only [archiveIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with {cases}
{branches}

theorem b13_remaining_of_residual332_radius_certificates
    (h : ∀ n, n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
      n ∉ archiveIDs → EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  LaneBResidual346Bridge.b13_remaining_of_residual346_radius_certificates
    (fun n hn => by
      by_cases hmem : n ∈ archiveIDs
      · exact certificateOf n hmem
      · exact h n hn hmem)

theorem main_of_residual332_radius_certificates_and_seven_classes
    (h : ∀ n, n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
      n ∉ archiveIDs → EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  LaneBResidual346Bridge.main_of_residual346_radius_certificates_and_seven_classes
    (fun n hn => by
      by_cases hmem : n ∈ archiveIDs
      · exact certificateOf n hmem
      · exact h n hn hmem) hclasses

theorem full_disk_bound_of_residual332_radius_certificates_and_seven_classes
    (h : ∀ n, n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs →
      n ∉ archiveIDs → EnergyTerminalBatchB13.ResidualRadiusCertificate n)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r →
      SourceExactRoot.sourceRadius ≤ r :=
  LaneBResidual346Bridge.full_disk_bound_of_residual346_radius_certificates_and_seven_classes
    (fun n hn => by
      by_cases hmem : n ∈ archiveIDs
      · exact certificateOf n hmem
      · exact h n hn hmem) hclasses

end
end N11Formalization.LaneBArchiveRefineAll14
#check @N11Formalization.LaneBArchiveRefineAll14.certificateOf
#check @N11Formalization.LaneBArchiveRefineAll14.b13_remaining_of_residual332_radius_certificates
#check @N11Formalization.LaneBArchiveRefineAll14.main_of_residual332_radius_certificates_and_seven_classes
#print axioms N11Formalization.LaneBArchiveRefineAll14.b13_remaining_of_residual332_radius_certificates
#print axioms N11Formalization.LaneBArchiveRefineAll14.full_disk_bound_of_residual332_radius_certificates_and_seven_classes
"""


def main() -> None:
    rows = [audit_source(node) for node in CANONICAL_IDS]
    text = emit(rows)
    if FORBIDDEN.search(text):
        raise SystemExit("emitted consumer contains a forbidden declaration")
    out = LEAN / "LaneBArchiveRefineAll14.lean"
    out.write_text(text, encoding="utf-8")
    for row in rows:
        print(row)
    print("consumer", out.name, "sha256", digest(text.encode()), "bytes", len(text.encode()))


if __name__ == "__main__":
    main()
