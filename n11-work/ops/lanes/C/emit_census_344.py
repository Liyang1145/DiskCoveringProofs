#!/usr/bin/env python3
"""Restore refinements 3825/3854 and emit the conditional 346 -> 344 bridge.

The archive sources are copied verbatim except for removal of the forbidden
`set_option maxHeartbeats 0` directive. This script performs source generation
and static assertions only; CI is required for elaboration and kernel credit.
"""
from pathlib import Path
import hashlib
import re
import subprocess

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
BRANCH = "origin/ci/n11-build"
ARCHIVE = "ci-n11/drafts/energy/N11Formalization"
IDS = (3825, 3854)
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b")

CHAIN = """    EnergyTerminalResidualCensusRefine346.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine348.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine350.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine352.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine354.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine356.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine358.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine360.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine362.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine364.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine366.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine368.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine371.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff"""


def archive_source(node: int) -> bytes:
    rel = f"{ARCHIVE}/EnergyRefineN{node:04d}.lean"
    source = subprocess.check_output(
        ["git", "show", f"{BRANCH}:{rel}"], cwd=HERE.parents[3])
    directive = b"set_option maxHeartbeats 0\n"
    assert source.count(directive) == 1, node
    source = source.replace(directive, b"", 1)
    text = source.decode()
    assert not FORBIDDEN.search(text), node
    assert f"def newIDs : Finset (Fin 5011) := {{{node}}}" in text, node
    assert f"(DBMSourceTree.data {node}).terminal = true" in text, node
    return source


def wrapper_files(node: int) -> None:
    wrapper = (LEAN / "EnergyTerminalBatchB13Refine3853.lean").read_text()
    wrapper_main = (LEAN / "EnergyTerminalBatchB13Refine3853Main.lean").read_text()
    wrapper = wrapper.replace("3853", str(node))
    wrapper_main = wrapper_main.replace("3853", str(node))
    assert "3853" not in wrapper and "3853" not in wrapper_main, node
    (LEAN / f"EnergyTerminalBatchB13Refine{node}.lean").write_text(wrapper)
    (LEAN / f"EnergyTerminalBatchB13Refine{node}Main.lean").write_text(wrapper_main)


def member_block(node: int) -> str:
    return f"""private theorem mem_346_{node} :
    ({node} : Fin 5011) ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs := by
  rw [
{CHAIN}]
  repeat' first
    | exact EnergyRefineN{node:04d}.terminal
    | exact not_sharp_{node}
    | exact EnergyTerminalBatchB13Refine{node}.not_paid_{node}
    | decide
    | constructor
"""


TEXT = f"""import N11Formalization.EnergyTerminalResidualCensusRefine346
import N11Formalization.EnergyTerminalBatchB13Refine3825
import N11Formalization.EnergyTerminalBatchB13Refine3854

/-! Remove restored archive refinements 3825 and 3854 from the 346-id residual
interface, leaving an exact conditional residual of 344 ids. The restored source
modules are copied verbatim except for removal of an unbounded-heartbeat
directive; they remain CI pending and this module makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine344
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {{3825, 3854}}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine346.refinedResidualIDs \\ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3825 : (3825 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_3854 : (3854 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

{member_block(3825)}
{member_block(3854)}
private theorem newRefineIDs_subset_346 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine346.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact mem_346_3825
  · exact mem_346_3854

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 344 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_346,
    EnergyTerminalResidualCensusRefine346.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine346.refinedResidualIDs ∧
        n ≠ 3825 ∧ n ≠ 3854 := by
  rw [refinedResidualIDs, Finset.mem_sdiff, newRefineIDs,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, n ∈ refinedResidualIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →
          SourceExactRoot.sourceRadius ≤ r

theorem remaining_of_radius_certificates
    (h : ∀ n, n ∈ refinedResidualIDs →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    RemainingTerminalRadius := by
  intro n hn y hy0 hy1 hc C Z r hf
  exact (h n hn).radius y hy0 hy1 hc C Z r hf

theorem b13_remaining_of_residual344 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine346.b13_remaining_of_residual346
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3825 : n = 3825
  · subst n
    exact (EnergyRefineN3825.new_radius 3825 (by simp [EnergyRefineN3825.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3854 : n = 3854
    · subst n
      exact (EnergyRefineN3854.new_radius 3854 (by simp [EnergyRefineN3854.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3825, hn3854⟩)
        y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine344
#check @N11Formalization.EnergyTerminalResidualCensusRefine344.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine344.b13_remaining_of_residual344
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine344.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine344.b13_remaining_of_residual344
"""


def main() -> None:
    for node in IDS:
        source = archive_source(node)
        path = LEAN / f"EnergyRefineN{node}.lean"
        path.write_bytes(source)
        print(node, len(source), hashlib.sha256(source).hexdigest())
        wrapper_files(node)
    output = LEAN / "EnergyTerminalResidualCensusRefine344.lean"
    output.write_text(TEXT)
    assert not FORBIDDEN.search(TEXT)
    print(output, hashlib.sha256(output.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
