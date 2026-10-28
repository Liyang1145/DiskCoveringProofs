#!/usr/bin/env python3
"""Static interface audit for the generated C450 chain-completion modules.

This does not replace CI kernel checking. It checks the source facts that a
local build cannot cheaply obtain here: all 36 data indices, every transfer
signature, the emitted call order, and determinism of the emitter.
"""

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


if __name__ == "__main__":
    main()
