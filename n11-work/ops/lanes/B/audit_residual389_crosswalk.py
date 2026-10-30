#!/usr/bin/env python3
"""Bind lane B's literal B13 residual census to lane C's residual records.

This is a source-inventory audit, not a Lean elaboration result and not a
payment of any residual cell.  It checks the exact ID sets, ordering, hashes,
and local-record coverage, and writes a deterministic crosswalk report.
"""

import hashlib
import json
import re
from pathlib import Path


LANE = Path(__file__).resolve().parent
ROOT = LANE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
BASE = LEAN / "EnergyTerminalResidualCensusBase.lean"
B13 = LEAN / "EnergyTerminalBatchB13.lean"
CLOSURE_REPORT = LANE / "audit_b13_closure-report.json"
LANE_C_CENSUS = ROOT / "n11-work/ops/lanes/C/residual389-census.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def ids_sha256(ids: list[int]) -> str:
    return hashlib.sha256(",".join(map(str, ids)).encode()).hexdigest().upper()


def literal_chunks() -> list[list[int]]:
    text = BASE.read_text(encoding="utf-8")
    chunks = []
    for index in range(4):
        match = re.search(
            rf"^def chunk{index}\s*:\s*Finset \(Fin 5011\)\s*:=\s*\{{([^}}]*)\}}",
            text,
            re.MULTILINE,
        )
        if match is None:
            raise SystemExit(f"missing chunk{index} in {BASE.name}")
        chunks.append([int(x) for x in re.findall(r"\d+", match.group(1))])
    return chunks


def main() -> None:
    chunks = literal_chunks()
    lane_b_ids = sorted(set().union(*map(set, chunks)))
    lane_c = json.loads(LANE_C_CENSUS.read_text(encoding="utf-8"))
    lane_c_ids = lane_c["residual_ids"]
    closure = json.loads(CLOSURE_REPORT.read_text(encoding="utf-8"))

    lane_b_hash = ids_sha256(lane_b_ids)
    lane_c_hash = ids_sha256(lane_c_ids)
    closure_hash = closure["digest"]["residual_ids_sha256"]
    chunk_slices = [lane_b_ids[i * 100:(i + 1) * 100 if i < 3 else len(lane_b_ids)]
                    for i in range(4)]
    local_records = {record["id"]: record for record in lane_c["local_survey_records"]}

    checks = {
        "lane_b_literal_count_389": len(lane_b_ids) == 389,
        "lane_c_census_count_389": len(lane_c_ids) == 389,
        "lane_b_chunk_sizes_100_100_100_89":
            [len(chunk) for chunk in chunks] == [100, 100, 100, 89],
        "lane_b_chunks_sorted_and_disjoint_contiguous_slices":
            all(chunk == expected for chunk, expected in zip(chunks, chunk_slices)),
        "lane_b_equals_lane_c": lane_b_ids == sorted(lane_c_ids),
        "lane_b_hash_equals_lane_c": lane_b_hash == lane_c_hash,
        "lane_c_declared_hash_matches": lane_c["residual_ids_sha256"] == lane_c_hash,
        "lane_b_hash_equals_closure": lane_b_hash == closure_hash,
        "closure_count_389": closure["counts"]["residual"] == 389,
        "local_record_ids_subset_lane_c": set(local_records) <= set(lane_c_ids),
        "local_record_count_7": len(local_records) == 7,
        "local_records_claim_no_pass":
            all(not record["pass_recorded"] for record in local_records.values()),
        "missing_local_record_count_382":
            lane_c["missing_local_survey_records"] == 382,
    }
    failed = [name for name, passed in checks.items() if not passed]

    chunk_of = {node_id: index for index, chunk in enumerate(chunks) for node_id in chunk}
    crosswalk = []
    for node_id in lane_b_ids:
        record = local_records.get(node_id)
        crosswalk.append({
            "id": node_id,
            "lane_b_chunk": chunk_of[node_id],
            "lane_c_record": False if record is None else True,
            "pass_recorded": None if record is None else record["pass_recorded"],
            "excluded_for_any_row_count":
                None if record is None else record["excluded_for_any_row_count"],
        })

    report = {
        "scope": "exact source-ID crosswalk only; no Lean elaboration and no payment of residual cells",
        "source_sha256": {
            "EnergyTerminalResidualCensusBase.lean": sha256(BASE),
            "EnergyTerminalBatchB13.lean": sha256(B13),
            "audit_b13_closure-report.json": sha256(CLOSURE_REPORT),
            "residual389-census.json": sha256(LANE_C_CENSUS),
        },
        "ids_sha256": lane_b_hash,
        "counts": {
            "lane_b_literal": len(lane_b_ids),
            "lane_c_census": len(lane_c_ids),
            "matched": len(set(lane_b_ids) & set(lane_c_ids)),
            "local_survey_records": len(local_records),
            "missing_local_survey_records": len(lane_b_ids) - len(local_records),
        },
        "chunk_sizes": [len(chunk) for chunk in chunks],
        "checks": checks,
        "unmatched_lane_b_ids": sorted(set(lane_b_ids) - set(lane_c_ids)),
        "unmatched_lane_c_ids": sorted(set(lane_c_ids) - set(lane_b_ids)),
        "crosswalk": crosswalk,
    }
    (LANE / "audit_residual389_crosswalk-report.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )
    if failed:
        raise SystemExit("FAILED: " + ", ".join(failed))
    print(json.dumps(report["counts"], sort_keys=True))
    print(f"all {len(checks)} crosswalk checks passed; ids_sha256={lane_b_hash}")


if __name__ == "__main__":
    main()
