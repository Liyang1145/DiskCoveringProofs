#!/usr/bin/env python3
"""Emit the two C450 chain-completion modules from the checked segment telescope."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[3] / "lean" / "N11Formalization"


def nested_transfer() -> str:
    lines = []
    indent = "  "
    opens = 0
    for source in range(12, 37):
        lines.append(
            f"{indent}C450Source{source}Segment."
            f"source{source - 1}_remaining_of_remaining ("
        )
        indent += "  "
        opens += 1
    lines.append(f"{indent}source36_remaining")
    for _ in range(opens):
        indent = indent[:-2]
        lines.append(f"{indent})")
    return "\n".join(lines)


chain = f'''import N11Formalization.C450Source36Segment
import N11Formalization.C450NormalizedInterface

/-! Kernel-checked completion of the C450 source telescope.

`C450Source36Segment.remainingSegs` is `c450Segs.drop 36`, hence empty.  Applying
the 25 emitted predecessor-transfer lemmas from Source12 through Source36 turns
that vacuous tail into `C450Source11Segment.RemainingSourceObligation`, the
root's `h450`, without a new hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletion

open N11Formalization C450NormalizedInterface

theorem source36_remaining : C450Source36Segment.RemainingSourceObligation := by
  intro s hs
  have hlen : C450Source36Segment.remainingSegs.length = 0 :=
    C450Source36Segment.remaining_count
  cases h : C450Source36Segment.remainingSegs with
  | nil =>
      rw [h] at hs
      simp at hs
  | cons a as =>
      rw [h] at hlen
      exfalso
      exact absurd hlen (by simp)

theorem h450 : C450Source11Segment.RemainingSourceObligation :=
{nested_transfer()}

theorem source_obligation : SourceObligation :=
  C450Source11Segment.source_of_remaining h450

theorem c450_atom : C450Atom :=
  C450Source11Segment.atom_of_remaining h450

theorem card_boundaryIdx_eq_nine {{c : Fin 11 → Point}} {{r : ℝ}}
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 :=
  C450NormalizedInterface.nine_of_source source_obligation hr hc

theorem exists_covers_ringLabels {{c : Fin 11 → Point}} {{r : ℝ}}
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11), Covers (fun j => c (p j)) r ∧
      DSHTopologyInterior.RingLabels (fun j => c (p j)) r :=
  C450NormalizedInterface.ringLabels_of_source source_obligation hr hc

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] := by
  cases h : C450Source36Segment.remainingSegs with
  | nil => rfl
  | cons a as =>
      have hlen := C450Source36Segment.remaining_count
      rw [h] at hlen
      exfalso
      exact absurd hlen (by simp)

theorem chain_step_count : (36 - 12) + 1 = 25 := rfl

end N11Formalization.C450ChainCompletion
#check @N11Formalization.C450ChainCompletion.source36_remaining
#check @N11Formalization.C450ChainCompletion.h450
#check @N11Formalization.C450ChainCompletion.source_obligation
#check @N11Formalization.C450ChainCompletion.c450_atom
#check @N11Formalization.C450ChainCompletion.card_boundaryIdx_eq_nine
#check @N11Formalization.C450ChainCompletion.exists_covers_ringLabels
#print axioms N11Formalization.C450ChainCompletion.h450
#print axioms N11Formalization.C450ChainCompletion.source_obligation
#print axioms N11Formalization.C450ChainCompletion.c450_atom
'''

main_text = '''import N11Formalization.C450ChainCompletion
import N11Formalization.ActualMetricClassReduction

/-! The C450 completion consumer: the chain's `h450` is checked against the
public interface type and fed to the existing seven-class main theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ChainCompletionMain

open N11Formalization

theorem h450_type_witness : C450Source11Segment.RemainingSourceObligation :=
  C450ChainCompletion.h450

theorem main_of_energy_and_seven_classes
    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  ActualMetricClassReduction.main_of_seven_class_certificates
    C450ChainCompletion.h450 henergy hclasses

end N11Formalization.C450ChainCompletionMain
#check @N11Formalization.C450ChainCompletionMain.main_of_energy_and_seven_classes
#print axioms N11Formalization.C450ChainCompletionMain.main_of_energy_and_seven_classes
'''


def main() -> None:
    assert ROOT.is_dir(), ROOT
    chain_name = "C450ChainCompletion.lean"
    main_name = "C450ChainCompletionMain.lean"
    for name, text in ((chain_name, chain), (main_name, main_text)):
        path = ROOT / name
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"wrote {path} ({len(text.encode('utf-8'))} bytes)")
    joined = chain + main_text
    forbidden = ("sorry", "admit", "axiom ", "native_decide", "ofReduceBool", "implemented_by")
    hits = [token for token in forbidden if token in joined]
    assert not hits, hits
    assert chain.count("source{source - 1}") == 0
    nest = nested_transfer()
    assert nest.count("remaining_of_remaining (") == 25
    assert nest.count("(") == nest.count(")")
    for source in range(12, 37):
        segment = ROOT / f"C450Source{source}Segment.lean"
        declaration = f"source{source - 1}_remaining_of_remaining"
        assert declaration in segment.read_text(encoding="utf-8"), (segment, declaration)


if __name__ == "__main__":
    main()
