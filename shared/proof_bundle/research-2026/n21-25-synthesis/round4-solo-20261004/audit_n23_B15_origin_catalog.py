"""Stdlib independent full-byte-catalog partition by actual-cover necessity.

No grouping, numeric solver, force proposer, or origin classifier is imported.
The historical enumerator's completeness induction and the arbitrary-cover
transport remain upstream obligations; this audit does not certify them.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import Catalog, sha, no_duplicate_keys
from n25_outer_search import read, publish, unchanged

assert __debug__
N, B, TOTAL = 23, 15, 16790546
CATALOG_SHA = "d1489120333b36e31e792bb6b277cd11c2a12fe20f6a51100999ab80f0f71344"
UPPER = F(249953776586051, 10**15)


def radius_gate(value):
    value = F(value)
    assert 0 < value < F(1, 4), "origin partition requires a strict quarter-radius gap"
    return 1-4*value


def input_gate(dataset):
    assert dataset.is_relative_to(ROOT)
    recoverypath = dataset / "VERIFIED.json"
    recovery = read(recoverypath)
    assert recovery["verified"]
    assert recovery["schema"] == "isolated-N23-B15-five-member-archive-byte-recovery-v1"
    assert recovery["source_sha256"] == sha(ROOT / "recover_n23_B15_archive_dataset.py")
    assert recovery["all_recovered_bytes_match_exact_original_asset_manifest"]
    selected = {row["recovered_relative_to_round4"]: row for row in recovery["selected_members"]}
    paths = [dataset / "CATALOG/N23-B15-dfs.json", dataset / "CATALOG/SUMMARY.json"]
    for path in paths:
        record = selected[path.relative_to(ROOT).as_posix()]
        assert path.stat().st_size == record["bytes"] and sha(path) == record["sha256"]
    catalogpath, summarypath = paths
    assert catalogpath.stat().st_size == 3961515667 and sha(catalogpath) == CATALOG_SHA
    original = read(summarypath)
    assert (original["N"], original["B"], original["orbits"]) == (N, B, TOTAL)
    assert original["complete"] and original["catalog_sha256"] == CATALOG_SHA
    assert original["catalogue_completeness_requires_written_induction"]
    assert original["source_sha256"] == sha(HIGH / "peel_degree.cpp")
    assert original["stream_reader_sha256"] == sha(HIGH / "stream_catalog.py")
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constantspath)
    assert constants["verified"] and constants["N"] == N
    assert F(constants["radius_upper"]) == UPPER
    assert sha(constantspath) == original["constants_sha256"]
    gap = radius_gate(constants["radius_upper"])
    controlpath = ROOT / "n23-n24-cover-origin-necessity-controls-20261005-v1/VERIFIED.json"
    controls = read(controlpath)
    assert controls["verified"] and controls["schema"] == "N23-N24-actual-cover-origin-necessity-controls-v1"
    unchanged(controls["files_relative_to_workspace"])
    control = next(row for row in controls["recorded_attaining_cases"] if row["N"] == N)
    assert control["B"] == B and control["exposed_centers"] == N-1
    assert control["recorded_attaining_full_graph_explicitly_retained"]
    catalog = Catalog(catalogpath)
    header = catalog.header
    assert (header["N"], header["B"], header["orbits"]) == (N, B, TOTAL)
    assert header["complete"] and header["screen"] and header["root_degree_prune"]
    assert header["scale"] == constants["angle_scale"] and header["caps"] == constants["angle_caps"]
    assert header["calls"] == original["calls"] and header["mode"] == original["mode"]
    catalog.stream.close()
    boundpaths = [
        recoverypath, catalogpath, summarypath, constantspath, controlpath,
        HIGH / "stream_catalog.py", HIGH / "peel_degree.cpp",
        ROOT / "N23-N24-UNEXPOSED-ORIGIN-SOURCE.md",
        ROOT / "N25-COLLAR-COVER-INTERFACE.md",
    ]
    return catalogpath, gap, {str(path): sha(path) for path in boundpaths}


def ledger_header(kind, digest):
    return {
        "schema": "frozen-N23-B15-full-type-origin-partition-ledger-v1",
        "N": N, "B": B, "catalog_sha256": digest, "kind": kind,
        "actual_cover_necessity_only_not_weak_geometry": True,
    }


def independent_exposure(faces, n=N, b=B):
    """Count only triangles meeting the ORIGINAL boundary center labels."""
    assert type(n) is int and type(b) is int and 3 <= b <= n <= 25
    assert faces and faces == sorted(set(faces))
    boundary, used = (1 << b)-1, 0
    for triangle in faces:
        assert type(triangle) is int and 0 < triangle < 1 << n and triangle.bit_count() == 3
        if triangle & boundary:
            used |= triangle
    return boundary | used


def scan_rows(rows, obstruction_stream, pending_stream, total, progress=False):
    counts = Counter()
    paid = pending = seen = 0
    started = time.monotonic()
    for index, full in rows:
        assert index == seen, "source index gap or duplicate"
        mask = independent_exposure(full["faces"])
        is_obstruction = mask == (1 << N)-1
        stream = obstruction_stream if is_obstruction else pending_stream
        line = stream.readline()
        assert line, ("missing partition row", index)
        record = json.loads(line, object_pairs_hook=no_duplicate_keys)
        assert set(record) == {"index", "exposed_mask"}
        assert type(record["index"]) is int and record["index"] == index, (
            "partition index gap, duplication, or wrong status", index, record)
        assert type(record["exposed_mask"]) is int and record["exposed_mask"] == mask, (
            "incorrect exposure; internal-only triangles cannot expose centers", index)
        paid += is_obstruction
        pending += not is_obstruction
        counts[mask.bit_count()] += 1
        seen += 1
        if progress and seen % 250000 == 0:
            print("N23/B15 independently audited", seen, "origin obstructions", paid,
                  "pending", pending, "seconds", round(time.monotonic()-started, 2), flush=True)
    assert seen == total == paid+pending, "incomplete source row scan"
    assert not obstruction_stream.read(1) and not pending_stream.read(1), "extra partition rows"
    return {"catalog_types_scanned": seen, "actual_cover_origin_obstructions": paid,
            "pending_full_types": pending, "exposed_center_histogram": dict(sorted(counts.items()))}


def audit(dataset, proposalpath, output):
    assert output.is_relative_to(ROOT) and not output.exists()
    catalogpath, gap, frozen = input_gate(dataset)
    proposal = read(proposalpath)
    assert proposal["schema"] == "proposal-frozen-N23-B15-full-type-origin-partition-v1"
    assert (proposal["N"], proposal["B"], proposal["catalog_types"]) == (N, B, TOTAL)
    assert proposal["catalog_sha256"] == CATALOG_SHA and F(proposal["radius_upper"]) == UPPER
    assert proposal["source_sha256"] == sha(ROOT / "partition_n23_B15_origin_catalog.py")
    for path, digest in frozen.items():
        assert proposal["frozen_files"][path] == digest
    obstructions = proposalpath.parent / "ORIGIN-OBSTRUCTIONS.jsonl"
    pending = proposalpath.parent / "PENDING.jsonl"
    assert proposal["origin_obstructions_sha256"] == sha(obstructions)
    assert proposal["pending_sha256"] == sha(pending)
    for path in (proposalpath, obstructions, pending, Path(__file__).resolve(),
                 ROOT / "partition_n23_B15_origin_catalog.py"):
        frozen[str(path)] = sha(path)
    output.mkdir()
    catalog = Catalog(catalogpath)
    with obstructions.open(encoding="ascii") as paid_stream, pending.open(encoding="ascii") as pending_stream:
        assert json.loads(next(paid_stream), object_pairs_hook=no_duplicate_keys) == ledger_header(
            "actual-cover-origin-obstruction", CATALOG_SHA)
        assert json.loads(next(pending_stream), object_pairs_hook=no_duplicate_keys) == ledger_header(
            "not-paid-by-origin-condition", CATALOG_SHA)
        result = scan_rows(catalog.rows(), paid_stream, pending_stream, TOTAL, progress=True)
    assert catalog.finished
    assert result["actual_cover_origin_obstructions"] == proposal["actual_cover_origin_obstructions"]
    assert result["pending_full_types"] == proposal["pending_full_types"]
    assert result["exposed_center_histogram"] == {
        int(key): value for key, value in proposal["exposed_center_histogram"].items()}
    for path, digest in frozen.items():
        assert sha(path) == digest, ("bound bytes changed", path)
    forbidden = ("numpy", "scipy", "clarabel", "mpmath", "group_catalog",
                 "small_order_cover_origin", "refine_collar_origin")
    assert not any(name in sys.modules for name in forbidden)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "independent-frozen-N23-B15-full-type-origin-partition-v1",
        "N": N, "B": B, **result,
        "all_16790546_declared_rows_fresh_stream_scanned": True,
        "source_end_of_file_and_declared_orbit_count_checked": True,
        "all_obstruction_and_pending_indices_partitioned_once": True,
        "all_exposure_masks_independently_recomputed_from_actual_faces": True,
        "pure_internal_faces_never_counted_as_exposure": True,
        "radius_upper": str(UPPER), "strict_gap_1_minus_4U": str(gap),
        "catalog_sha256": CATALOG_SHA, "proposal_sha256": sha(proposalpath),
        "origin_obstructions_sha256": sha(obstructions), "pending_sha256": sha(pending),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "actual_arbitrary_cover_auxiliary_rod_interface_required": True,
        "not_a_standalone_geometric_full_or_weak_graph_exclusion": True,
        "historical_catalog_completeness_induction_not_proved_here": True,
        "pair_outer_mappings_and_old_force_trees_not_accepted_here": True,
        "remaining_lower_bounds_not_paid_here": True, "global_optimality_proved": False,
    })
    print("N23/B15 complete frozen catalog origin partition independently accepted:",
          result["actual_cover_origin_obstructions"], "cover obstructions;",
          result["pending_full_types"], "pending", flush=True)


def main():
    ap = argparse.ArgumentParser()
    for name in ("dataset", "proposal", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    audit(args.dataset.resolve(), args.proposal.resolve(), args.output.resolve())


if __name__ == "__main__":
    main()
