#!/usr/bin/env python3
"""Static interface audit for the generated C450 chain-completion modules.

This does not replace CI kernel checking. It checks the source facts that a
local build cannot cheaply obtain here: all 36 data indices, every transfer
signature, the emitted call order, and determinism of the emitter.
"""

import hashlib
import importlib.util
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"


def load_emitter():
    spec = importlib.util.spec_from_file_location(
        "emit_chain_completion", HERE / "emit_chain_completion.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def one(pattern, text, what):
    matches = list(re.finditer(pattern, text, flags=re.DOTALL))
    assert len(matches) == 1, (what, len(matches))
    return matches[0]


def main():
    emitter = load_emitter()

    data = (LEAN / "DSHTenBoundaryData.lean").read_text(encoding="utf-8")
    start = data.index("def c450Segs")
    end = data.index("\n]\n", start) + 3
    records = data[start:end].count("{ eLo :=")
    assert records == 36, records

    for source in range(11, 37):
        data_name = f"C450Source{source}Data.lean"
        data_text = (LEAN / data_name).read_text(encoding="utf-8")
        index = source - 1
        assert f"c450Segs[{index}]? = some source{source}" in data_text, data_name

        segment_name = f"C450Source{source}Segment.lean"
        segment = (LEAN / segment_name).read_text(encoding="utf-8")
        if source >= 12:
            assert f"import N11Formalization.C450Source{source - 1}Segment" in segment, segment_name
            declaration = f"source{source - 1}_remaining_of_remaining"
            transfer = one(
                rf"theorem {declaration} \(hr : RemainingSourceObligation\) :\s*"
                rf"C450Source{source - 1}Segment\.RemainingSourceObligation := by\s*"
                rf"(.*?)(?=\ntheorem |\ndef |\nend )",
                segment,
                declaration,
            ).group(1)
            assert "intro s hs" in transfer, declaration
            assert f"source{source}_paid" in transfer, declaration
            assert "hr s" in transfer, declaration

    tail = (LEAN / "C450Source36Segment.lean").read_text(encoding="utf-8")
    assert "def remainingSegs : List TenSeg := c450Segs.drop 36" in tail
    assert "theorem remaining_count : remainingSegs.length = 0" in tail

    chain = (LEAN / "C450ChainCompletion.lean").read_text(encoding="utf-8")
    main_text = (LEAN / "C450ChainCompletionMain.lean").read_text(encoding="utf-8")
    assert chain == emitter.chain, "C450ChainCompletion.lean is not emitter output"
    assert main_text == emitter.main_text, "C450ChainCompletionMain.lean is not emitter output"

    expected_sha256 = {
        "C450ChainCompletion.lean":
            "935dcd6a0078ad0216e8e195e092c033cf2be7b46deb0d22b7d7cbd05000f191",
        "C450ChainCompletionMain.lean":
            "942dd90f69781a7ce1d57c5a393c3c11626cfe4135b30c5834fb2656ca3b6c03",
    }
    for name, expected in expected_sha256.items():
        digest = hashlib.sha256((LEAN / name).read_bytes()).hexdigest()
        assert digest == expected, (name, digest)

    assert chain.startswith(
        "import N11Formalization.C450Source36Segment\n"
        "import N11Formalization.C450NormalizedInterface\n"
    ), "chain import closure drifted"
    assert main_text.startswith(
        "import N11Formalization.C450ChainCompletion\n"
        "import N11Formalization.ActualMetricClassReduction\n"
    ), "main import closure drifted"

    targets = (HERE / "TARGETS.txt").read_text(encoding="utf-8").splitlines()
    targets = [line.strip() for line in targets if line.strip() and not line.startswith("#")]
    assert targets == [
        "N11Formalization.C450ChainCompletion",
        "N11Formalization.C450ChainCompletionMain",
    ], targets

    calls = re.findall(
        r"C450Source(\d+)Segment\.source(\d+)_remaining_of_remaining \(", chain
    )
    assert calls == [(str(n), str(n - 1)) for n in range(12, 37)], calls
    assert chain.count("remaining_of_remaining (") == 25
    assert chain.count("(") == chain.count(")")
    assert "theorem h450 : C450Source11Segment.RemainingSourceObligation :=" in chain
    assert "C450Source11Segment.source_of_remaining h450" in chain
    assert (
        "ActualMetricClassReduction.main_of_seven_class_certificates\n"
        "    C450ChainCompletion.h450 henergy hclasses" in main_text
    )

    forbidden = ("sorry", "admit", "axiom ", "native_decide", "ofReduceBool",
                 "implemented_by", "maxHeartbeats 0")
    for token in forbidden:
        assert token not in chain and token not in main_text, token

    print("PASS: c450Segs has 36 records; Source11..36 data indices are 10..35")
    print("PASS: 25 predecessor transfers have exact signatures, consume sourceN_paid, and call order is exact")
    print("PASS: drop 36 is the vacuous tail; h450 reaches Source11")
    print("PASS: both Lean modules are deterministic emitter output; no forbidden tokens")
    print("PASS: both Lean modules match their pinned SHA256 bytes")
    print("PASS: direct import closure and CI target order are exact")


if __name__ == "__main__":
    main()
