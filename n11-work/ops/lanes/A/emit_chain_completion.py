#!/usr/bin/env python3
"""Emit the C450 telescope as five small, independently checked modules.

The transfer functions are assembled in groups of five.  This keeps every
elaborated proof term small while preserving the public
`C450ChainCompletion.h450` interface.  Axiom printing is deliberately kept out
of these modules: traversing the full telescope at elaboration time is the
memory-heavy operation CI must avoid.
"""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[3] / "lean" / "N11Formalization"


def nested_transfer(sources: list[int], final: str, indent: str = "  ") -> str:
    lines: list[str] = []
    for source in sources:
        lines.append(
            f"{indent}C450Source{source}Segment."
            f"source{source - 1}_remaining_of_remaining ("
        )
        indent += "  "
    lines.append(f"{indent}{final}")
    for _ in sources:
        indent = indent[:-2]
        lines.append(f"{indent})")
    return "\n".join(lines)


def module_preamble(name: str, imports: list[str], doc: str) -> str:
    head = "".join(f"import {item}\n" for item in imports)
    return f'''{head}
/-! {doc} -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.{name}
'''


endpoint = module_preamble(
    "C450ChainCompletionEndpoint",
    ["N11Formalization.C450Source36Segment"],
    "The vacuous C450 source-36 endpoint, isolated from all telescope transfers.",
) + f'''open N11Formalization

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] :=
  List.eq_nil_of_length_eq_zero C450Source36Segment.remaining_count

theorem source36_remaining : C450Source36Segment.RemainingSourceObligation := by
  intro s hs
  rw [source36_remaining_vacuous] at hs
  cases hs

end N11Formalization.C450ChainCompletionEndpoint
#check @N11Formalization.C450ChainCompletionEndpoint.source36_remaining
'''

tail = module_preamble(
    "C450ChainCompletionTail",
    ["N11Formalization.C450ChainCompletionEndpoint"],
    "The first five C450 telescope transfers (36 through 32).",
) + f'''open N11Formalization

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] :=
  C450ChainCompletionEndpoint.source36_remaining_vacuous

theorem source36_remaining : C450Source36Segment.RemainingSourceObligation :=
  C450ChainCompletionEndpoint.source36_remaining

theorem source31_remaining : C450Source31Segment.RemainingSourceObligation :=
{nested_transfer([32, 33, 34, 35, 36], "source36_remaining")}

end N11Formalization.C450ChainCompletionTail
#check @N11Formalization.C450ChainCompletionTail.source36_remaining
#check @N11Formalization.C450ChainCompletionTail.source31_remaining
'''

mid1 = module_preamble(
    "C450ChainCompletionMid1",
    ["N11Formalization.C450ChainCompletionTail"],
    "C450 telescope transfers 31 through 27.",
) + f'''open N11Formalization

theorem source26_remaining : C450Source26Segment.RemainingSourceObligation :=
{nested_transfer([27, 28, 29, 30, 31], "C450ChainCompletionTail.source31_remaining")}

end N11Formalization.C450ChainCompletionMid1
#check @N11Formalization.C450ChainCompletionMid1.source26_remaining
'''

mid2 = module_preamble(
    "C450ChainCompletionMid2",
    ["N11Formalization.C450ChainCompletionMid1"],
    "C450 telescope transfers 26 through 22.",
) + f'''open N11Formalization

theorem source21_remaining : C450Source21Segment.RemainingSourceObligation :=
{nested_transfer([22, 23, 24, 25, 26], "C450ChainCompletionMid1.source26_remaining")}

end N11Formalization.C450ChainCompletionMid2
#check @N11Formalization.C450ChainCompletionMid2.source21_remaining
'''

mid3 = module_preamble(
    "C450ChainCompletionMid3",
    ["N11Formalization.C450ChainCompletionMid2"],
    "C450 telescope transfers 21 through 17.",
) + f'''open N11Formalization

theorem source16_remaining : C450Source16Segment.RemainingSourceObligation :=
{nested_transfer([17, 18, 19, 20, 21], "C450ChainCompletionMid2.source21_remaining")}

end N11Formalization.C450ChainCompletionMid3
#check @N11Formalization.C450ChainCompletionMid3.source16_remaining
'''

chain = module_preamble(
    "C450ChainCompletion",
    [
        "N11Formalization.C450ChainCompletionMid3",
        "N11Formalization.C450NormalizedInterface",
    ],
    "Final C450 transfers 16 through 12 and the public h450 consumer interface.",
) + f'''open N11Formalization C450NormalizedInterface

theorem source36_remaining : C450Source36Segment.RemainingSourceObligation :=
  C450ChainCompletionTail.source36_remaining

theorem source36_remaining_vacuous : C450Source36Segment.remainingSegs = [] :=
  C450ChainCompletionTail.source36_remaining_vacuous

theorem h450 : C450Source11Segment.RemainingSourceObligation :=
{nested_transfer([12, 13, 14, 15, 16], "C450ChainCompletionMid3.source16_remaining")}

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

theorem chain_step_count : (36 - 12) + 1 = 25 := rfl

end N11Formalization.C450ChainCompletion
#check @N11Formalization.C450ChainCompletion.h450
#check @N11Formalization.C450ChainCompletion.source_obligation
#check @N11Formalization.C450ChainCompletion.c450_atom
#check @N11Formalization.C450ChainCompletion.card_boundaryIdx_eq_nine
#check @N11Formalization.C450ChainCompletion.exists_covers_ringLabels
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
'''

MODULES = {
    "C450ChainCompletionEndpoint.lean": endpoint,
    "C450ChainCompletionTail.lean": tail,
    "C450ChainCompletionMid1.lean": mid1,
    "C450ChainCompletionMid2.lean": mid2,
    "C450ChainCompletionMid3.lean": mid3,
    "C450ChainCompletion.lean": chain,
    "C450ChainCompletionMain.lean": main_text,
}


def main() -> None:
    assert ROOT.is_dir(), ROOT
    forbidden = ("sorry", "admit", "axiom ", "native_decide", "ofReduceBool",
                 "implemented_by", "maxHeartbeats 0")
    for name, text in MODULES.items():
        hits = [token for token in forbidden if token in text]
        assert not hits, (name, hits)
        path = ROOT / name
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"wrote {path} ({len(text.encode('utf-8'))} bytes)")


if __name__ == "__main__":
    main()
