#!/usr/bin/env python3
"""Audit the source-index partition used by the residual census modules.

This is a static source check.  It verifies that the four emitted parts cover
every index in `Fin 5011` exactly once and that no kernel decision spans more
than the documented 111 source literals.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

LANE = Path(__file__).resolve().parent
LEAN = LANE.parents[2] / "lean" / "N11Formalization"
PARTS = [LEAN / f"EnergyTerminalResidualCensusC{index:02d}.lean" for index in range(1, 5)]
ASSEMBLY = LEAN / "EnergyTerminalResidualCensus.lean"
BASE = LEAN / "EnergyTerminalResidualCensusBase.lean"
LANE_C_CENSUS = LANE.parent / "C" / "residual389-census.json"
REPORT = LANE / "audit_census_blocks-report.json"
BLOCK = re.compile(
    r"theorem mem_iff_block(?P<block>\d{2}) \(n : Fin 5011\)\s+"
    r"\(hlo : (?P<lo>\d+) ≤ n\.val\) \(hhi : n\.val < (?P<hi>\d+)\)"
)
CHUNK = re.compile(r"def chunk\d : Finset \(Fin 5011\) := \{([^}]*)\}")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main() -> None:
    records: list[dict[str, object]] = []
    for part in PARTS:
        text = part.read_text(encoding="utf-8")
        for match in BLOCK.finditer(text):
            block = int(match.group("block"))
            records.append({
                "block": block,
                "file": part.name,
                "lo": int(match.group("lo")),
                "hi": int(match.group("hi")),
            })

    expected = [(index * 100, min((index + 1) * 100, 5011)) for index in range(51)]
    actual = sorted((int(record["block"]), int(record["lo"]), int(record["hi"]))
                    for record in records)
    expected_tuples = [(index, lo, hi) for index, (lo, hi) in enumerate(expected)]

    assembly = ASSEMBLY.read_text(encoding="utf-8")
    calls = [int(value) for value in re.findall(r"mem_iff_block(\d{2}) n ", assembly)]
    chunk_ids = [
        {int(value) for value in re.findall(r"\d+", match.group(1))}
        for match in CHUNK.finditer(BASE.read_text(encoding="utf-8"))
    ]
    lane_c_ids = set(json.loads(LANE_C_CENSUS.read_text(encoding="utf-8-sig"))["residual_ids"])
    chunk_union = set().union(*chunk_ids)
    covered = [index for lo, hi in expected for index in range(lo, hi)]
    widths = [hi - lo for lo, hi in expected]

    checks = {
        "fifty_one_blocks": len(records) == 51,
        "block_ranges_exact": actual == expected_tuples,
        "no_gaps_or_overlaps": len(covered) == 5011 and covered == list(range(5011)),
        "assembly_calls_each_block_once": sorted(calls) == list(range(51)),
        "max_kernel_width_100": max(widths) == 100,
        "short_final_block_11": widths[-1] == 11,
        "four_literal_chunks": len(chunk_ids) == 4,
        "chunk_sizes_100_100_100_89": [len(ids) for ids in chunk_ids] == [100, 100, 100, 89],
        "chunks_pairwise_disjoint": len(chunk_union) == sum(len(ids) for ids in chunk_ids),
        "chunks_match_lane_c_census": chunk_union == lane_c_ids,
    }
    result = {
        "scope": "static source partition audit; not Lean elaboration and not proof credit",
        "checks": checks,
        "ok": all(checks.values()),
        "blocks": records,
        "widths": {"min": min(widths), "max": max(widths), "sum": sum(widths)},
        "sha256": {
            path.name: sha256(path) for path in [*PARTS, BASE, ASSEMBLY, LANE_C_CENSUS]
        },
    }
    REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"ok": result["ok"], "checks": checks, **result["widths"]}, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
