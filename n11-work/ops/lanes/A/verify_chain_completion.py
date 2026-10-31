#!/usr/bin/env python3
"""Static audit of the split C450 telescope emitter and its CI targets."""

import hashlib
import importlib.util
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
ORDER = [
    "C450ChainCompletionEndpoint.lean",
    "C450ChainCompletionTail.lean",
    "C450ChainCompletionMid1.lean",
    "C450ChainCompletionMid2.lean",
    "C450ChainCompletionMid3.lean",
    "C450ChainCompletion.lean",
    "C450ChainCompletionMain.lean",
]


def load_emitter():
    spec = importlib.util.spec_from_file_location(
        "emit_chain_completion", HERE / "emit_chain_completion.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    emitter = load_emitter()
    assert list(emitter.MODULES) == ORDER, list(emitter.MODULES)

    data = (LEAN / "DSHTenBoundaryData.lean").read_text(encoding="utf-8")
    start = data.index("def c450Segs")
    end = data.index("\n]\n", start) + 3
    assert data[start:end].count("{ eLo :=") == 36

    for source in range(11, 37):
        data_text = (LEAN / f"C450Source{source}Data.lean").read_text(encoding="utf-8")
        assert f"c450Segs[{source - 1}]? = some source{source}" in data_text
        segment = (LEAN / f"C450Source{source}Segment.lean").read_text(encoding="utf-8")
        if source >= 12:
            assert f"import N11Formalization.C450Source{source - 1}Segment" in segment
            assert (
                f"theorem source{source - 1}_remaining_of_remaining "
                f"(hr : RemainingSourceObligation) :\n"
                f"    C450Source{source - 1}Segment.RemainingSourceObligation"
            ) in segment

    tail = (LEAN / "C450Source36Segment.lean").read_text(encoding="utf-8")
    assert "def remainingSegs : List TenSeg := c450Segs.drop 36" in tail
    assert "theorem remaining_count : remainingSegs.length = 0" in tail

    joined = ""
    for name in ORDER:
        text = (LEAN / name).read_text(encoding="utf-8")
        assert text == emitter.MODULES[name], f"{name} is not emitter output"
        digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
        print(f"{digest}  {name}")
        joined += text + "\n"

    assert "import N11Formalization.C450Source36Segment\n" in emitter.MODULES[ORDER[0]]
    assert "import N11Formalization.C450ChainCompletionEndpoint\n" in emitter.MODULES[ORDER[1]]
    assert "import N11Formalization.C450ChainCompletionTail\n" in emitter.MODULES[ORDER[2]]
    assert "import N11Formalization.C450ChainCompletionMid1\n" in emitter.MODULES[ORDER[3]]
    assert "import N11Formalization.C450ChainCompletionMid2\n" in emitter.MODULES[ORDER[4]]
    assert "import N11Formalization.C450ChainCompletionMid3\n" in emitter.MODULES[ORDER[5]]
    assert "import N11Formalization.C450ChainCompletion\n" in emitter.MODULES[ORDER[6]]

    calls = re.findall(
        r"C450Source(\d+)Segment\.source(\d+)_remaining_of_remaining \(", joined
    )
    assert len(calls) == 25, calls
    assert {(int(a), int(b)) for a, b in calls} == {
        (source, source - 1) for source in range(12, 37)
    }, calls
    assert len(set(calls)) == 25

    expected_outputs = {
        "C450ChainCompletionTail.lean": "C450Source31Segment.RemainingSourceObligation",
        "C450ChainCompletionMid1.lean": "C450Source26Segment.RemainingSourceObligation",
        "C450ChainCompletionMid2.lean": "C450Source21Segment.RemainingSourceObligation",
        "C450ChainCompletionMid3.lean": "C450Source16Segment.RemainingSourceObligation",
        "C450ChainCompletion.lean": "C450Source11Segment.RemainingSourceObligation",
    }
    theorem_names = {
        "C450ChainCompletionTail.lean": "source31_remaining",
        "C450ChainCompletionMid1.lean": "source26_remaining",
        "C450ChainCompletionMid2.lean": "source21_remaining",
        "C450ChainCompletionMid3.lean": "source16_remaining",
        "C450ChainCompletion.lean": "h450",
    }
    for name, typ in expected_outputs.items():
        assert f"theorem {theorem_names[name]} : {typ} :=" in emitter.MODULES[name]

    assert (
        "theorem source36_remaining_vacuous : "
        "C450Source36Segment.remainingSegs = [] :=\n"
        "  List.eq_nil_of_length_eq_zero C450Source36Segment.remaining_count"
        in emitter.MODULES[ORDER[0]]
    ), "Source36 endpoint must use the frozen zero-length count directly"
    assert (
        "theorem source36_remaining : "
        "C450Source36Segment.RemainingSourceObligation := by\n"
        "  intro s hs\n"
        "  rw [source36_remaining_vacuous] at hs\n"
        "  cases hs" in emitter.MODULES[ORDER[0]]
    ), "Source36 obligation must be derived from the vacuous list"
    assert (
        "theorem source36_remaining : "
        "C450Source36Segment.RemainingSourceObligation :=\n"
        "  C450ChainCompletionEndpoint.source36_remaining"
        in emitter.MODULES[ORDER[1]]
    ), "the transfer tail must consume the isolated Source36 endpoint"
    assert (
        "theorem source36_remaining_vacuous : "
        "C450Source36Segment.remainingSegs = [] :=\n"
        "  C450ChainCompletionTail.source36_remaining_vacuous" in emitter.MODULES[ORDER[5]]
    ), "the final interface must expose the vacuous Source36 endpoint"

    assert joined.count("remaining_of_remaining (") == 25
    assert joined.count("(") == joined.count(")")
    assert "C450Source11Segment.source_of_remaining h450" in emitter.MODULES[ORDER[5]]
    assert (
        "ActualMetricClassReduction.main_of_seven_class_certificates\n"
        "    C450ChainCompletion.h450 henergy hclasses"
    ) in emitter.MODULES[ORDER[6]]

    consumer = (LEAN / "ActualMetricClassReduction.lean").read_text(encoding="utf-8")
    assert (
        "theorem main_of_seven_class_certificates\n"
        "    (h450 : C450Source11Segment.RemainingSourceObligation)\n"
        "    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)\n"
        "    (hclasses : SevenClassExclusions) :\n"
        "    N11MainStatement SourceExactRoot.sourceRadius := by" in consumer or
        "theorem main_of_seven_class_certificates\n"
        "    (h450 : C450Source11Segment.RemainingSourceObligation)\n"
        "    (henergy : EnergyTerminalBatchB11.RemainingTerminalRadius)\n"
        "    (hclasses : SevenClassExclusions) :\n"
        "    N11MainStatement SourceExactRoot.sourceRadius :=" in consumer
    ), "ActualMetricClassReduction consumer signature drifted"

    forbidden = ("sorry", "admit", "axiom ", "native_decide", "ofReduceBool",
                 "implemented_by", "maxHeartbeats 0", "#print axioms")
    for token in forbidden:
        assert token not in joined, token

    targets = (HERE / "TARGETS.txt").read_text(encoding="utf-8").splitlines()
    targets = [line.strip() for line in targets if line.strip() and not line.startswith("#")]
    assert targets[:2] == [
        "N11Formalization.C450ChainCompletionMain",
        "N11Formalization.C450ChainCompletionAudit",
    ], targets

    root = (LEAN.parent / "N11Formalization.lean").read_text(encoding="utf-8")
    root_markers = [
        "-- HARK-MISSING (not in public assets; lane A reconstructs): "
        "import N11Formalization.C450ChainCompletion",
        "-- HARK-MISSING (not in public assets; lane A reconstructs): "
        "import N11Formalization.C450ChainCompletionMain",
    ]
    assert all(marker in root for marker in root_markers), (
        "C450 chain root-import markers drifted; supervisor must inspect the root"
    )

    print("PASS: five telescoping chunks contain all 25 transfers exactly once")
    print("PASS: chunk imports and output types reach Source31,26,21,16,11 in order")
    print("PASS: h450 retains the C450Source11 consumer interface")
    print("PASS: Source36 endpoint and ActualMetricClassReduction consumer signatures agree")
    print("PASS: all seven emitted modules are deterministic and top-level CI targets are exact")
    print("PASS: root still exposes both C450 HARK-MISSING markers (not yet imported)")
    print("PASS: no forbidden tokens and no proof-term-wide #print axioms in CI files")


if __name__ == "__main__":
    main()
