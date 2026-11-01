#!/usr/bin/env python3
"""Statically audit the bounded 20-block terminal census module.

This checks generated block coverage, disjointness-fact completeness, and the
literal cardinality sums.  It is not Lean elaboration and pays no radius.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
MODULE = ROOT / "n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean"
REPORT = LANE / "audit_terminal_census_blocks-report.json"


def main() -> None:
    text = MODULE.read_text(encoding="utf-8")
    embeds = {
        int(index): (int(width), int(start))
        for index, width, start in re.findall(
            r"def embed(\d+) \(n : Fin (\d+)\) : Fin 5011 := ⟨n\.val \+ (\d+), by omega⟩",
            text,
        )
    }
    census_cards = {
        int(index): int(card)
        for index, card in re.findall(
            r"theorem census(\d+)_card : census\1\.card = (\d+) := by\s+decide \+kernel", text
        )
    }
    filtered_census = {
        int(index): (int(width), int(embed))
        for index, width, embed in re.findall(
            r"def census(\d+) : Finset \(Fin (\d+)\) :=\s+"
            r"Finset\.univ\.filter fun n => "
            r"\(DBMSourceTree\.data \(embed(\d+) n\)\)\.terminal = true", text
        )
    }
    structural_specs = {
        int(index): int(width)
        for index, width in re.findall(
            r"theorem census(\d+)_spec \(n : Fin (\d+)\) :\s+"
            r"\(DBMSourceTree\.data \(embed\1 n\)\)\.terminal = true ↔ n ∈ census\1 := by\s+"
            r"simp only \[census\1, Finset\.mem_filter, Finset\.mem_univ, true_and\]", text
        )
    }
    block_cards = {
        int(index): int(card)
        for index, card in re.findall(
            r"theorem blockIDs(\d+)_card : blockIDs\1\.card = (\d+) := by", text
        )
    }
    lower = {
        int(index): int(bound)
        for index, bound in re.findall(
            r"theorem blockIDs(\d+)_lower : blockIDs\1 ⊆\s+"
            r"Finset\.univ\.filter \(fun n : Fin 5011 => (\d+) ≤ n\.val\)", text
        )
    }
    upper = {
        int(index): int(bound)
        for index, bound in re.findall(
            r"theorem blockIDs(\d+)_upper : blockIDs\1 ⊆\s+"
            r"Finset\.univ\.filter \(fun n : Fin 5011 => n\.val < (\d+)\)", text
        )
    }

    expected = {index: (256, index * 256) for index in range(19)}
    expected[19] = (147, 4864)
    facts = set(re.findall(r"^theorem (blockIDs_\d+_\d+_disjoint) ", text, re.M))
    expected_facts = {f"blockIDs_{i}_{j}_disjoint" for i in range(20) for j in range(i + 1, 20)}
    dispatcher = text[text.index("theorem blockIDs_pairwiseDisjoint") : text.index("theorem censusIDs_card")]
    dispatched = [
        name for name in re.findall(r"exact (blockIDs_\d+_\d+_disjoint)(?:\.symm)?", dispatcher)
    ]
    checks = {
        "twenty_embed_blocks": embeds == expected,
        "twenty_filtered_census_definitions": filtered_census == {
            index: (expected[index][0], index) for index in range(20)
        },
        "twenty_structural_census_specs": structural_specs == {
            index: expected[index][0] for index in range(20)
        },
        "twenty_literal_census_cards": len(census_cards) == 20,
        "literal_cards_equal_block_cards": census_cards == block_cards,
        "literal_cards_sum_2506": sum(census_cards.values()) == 2506,
        "block_bounds_contiguous": all(lower.get(i) == expected[i][1] for i in range(20))
        and all(upper.get(i) == expected[i][1] + expected[i][0] for i in range(19)),
        "all_190_disjointness_facts": facts == expected_facts,
        "all_190_facts_dispatched_both_orders": set(dispatched) == expected_facts
        and len(dispatched) == 380,
        "terminal_card_is_2506": bool(
            re.search(r"theorem terminalIDs_card : terminalIDs\.card = 2506 := by", text)
        ),
        "census_card_is_2506": bool(
            re.search(r"theorem censusIDs_card : censusIDs\.card = 2506 := by", text)
        ),
    }
    result = {
        "scope": "static generated-source audit; not Lean elaboration or kernel proof credit",
        "ok": all(checks.values()),
        "checks": checks,
        "block_widths": [expected[i][0] for i in range(20)],
        "literal_cardinality_sum": sum(census_cards.values()),
        "sha256": hashlib.sha256(MODULE.read_bytes()).hexdigest().upper(),
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
