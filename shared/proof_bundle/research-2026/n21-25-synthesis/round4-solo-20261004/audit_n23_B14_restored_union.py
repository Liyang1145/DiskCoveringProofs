"""Fresh bounded equality of every original B14 run and retained union layer.

This proves retained-run union equality only. The 8726 historic launcher
dependencies, exhaustive source induction, arbitrary-cover transport, and
all residual lower bounds are separate obligations.
"""
from pathlib import Path
import argparse
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from merge_paid_runs_bounded import RawCursor, check_union, phase_metadata
from paid_binary_residual import BinaryRows

assert __debug__


def ranges(count, fan_in):
    assert type(count) is int and count >= 0
    assert type(fan_in) is int and 2 <= fan_in <= 64
    return [(first, min(first+fan_in, count)) for first in range(0, count, fan_in)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--assets", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assets, controlpath, output = (getattr(args, name).resolve() for name in ("assets", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (assets, controlpath, output))
    assert not output.exists()
    reportpath = assets / "VERIFIED.json"
    recovered, controls = read(reportpath), read(controlpath)
    assert recovered["verified"] and recovered["schema"] == "isolated-N23-B14-all-original-union-asset-byte-recovery-v1"
    assert recovered["source_sha256"] == sha(ROOT / "recover_n23_B14_union_assets.py")
    assert (recovered["N"], recovered["B"], recovered["original_run_count"],
            recovered["retained_layer0_batches"]) == (23, 14, 779, 25)
    assert recovered["all_assets_match_original_archive_manifest_crc_size_and_sha256"]
    assert controls["verified"] and controls["schema"] == "restored-B14-union-adapter-finite-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_B14_union_adapter.py")
    assert controls["adapter_source_sha256"] == sha(Path(__file__))
    assert controls["frozen_merge_source_sha256"] == sha(HIGH / "merge_paid_runs_bounded.py")
    assert controls["frozen_reader_source_sha256"] == sha(HIGH / "paid_binary_residual.py")
    for path, digest in recovered["frozen_files"].items():
        assert sha(path) == digest
    records = {row["recovered_file"]: row for row in recovered["assets"]}
    assert len(records) == len(recovered["assets"]) == 811
    assert {path.name for path in (assets / "RUNS").iterdir()} == {f"run-{i}.bin" for i in range(779)}
    assert {path.name for path in (assets / "LAYER0").iterdir()} == {f"batch-{i}.bin" for i in range(25)}
    phasepath = assets / "SOURCE/N23-B14-pair-search.bin.building"
    phase = phase_metadata(phasepath)
    assert (phase["N"], phase["B"], phase["run_count"], phase["rows_to_runs"]) == (23, 14, 779, 77892318)
    assert phase["proof_prunes"] == 0 and phase["proof_payments"] == []
    assert phase["survivor_block_size"] == 100000 and phase["prefix_runs_replayed_and_compared"] == 0
    original = [assets / f"RUNS/run-{i}.bin" for i in range(779)]
    layer = [assets / f"LAYER0/batch-{i}.bin" for i in range(25)]
    target = assets / "FINAL/RESIDUAL.bin"
    catalogue = BinaryRows(target)
    header = dict(catalogue.header)
    catalogue.stream.close()
    expected_header = dict(phase, bounded_finalization=True, maximum_batch_input_files=32)
    assert {key: value for key, value in header.items() if key != "orbits"} == expected_header
    expected_total_size = 32+len(json.dumps(
        expected_header, separators=(",", ":"), ensure_ascii=True).encode("ascii"))+header["orbits"]*124
    assert target.stat().st_size == expected_total_size
    frozen = {str(path): sha(path) for path in (
        Path(__file__).resolve(), reportpath, controlpath, HIGH / "merge_paid_runs_bounded.py",
        HIGH / "paid_binary_residual.py", HIGH / "stream_catalog.py")}
    for relative, record in records.items():
        path = (assets / relative).resolve()
        assert path.is_relative_to(assets) and path.stat().st_size == record["bytes"]
        assert sha(path) == record["sha256"], ("restored original bytes changed", relative)
        frozen[str(path)] = record["sha256"]
    output.mkdir()
    started = time.monotonic()
    receipts = []
    source_rows = 0
    with (output / "BATCHES.jsonl").open("x", encoding="ascii") as ledger:
        for batch, (first, end) in enumerate(ranges(779, 32)):
            paths = original[first:end]
            batch_rows = 0
            for index, path in enumerate(paths, first):
                cursor = RawCursor(path, 23, 14)
                assert cursor.count == (100000 if index < 778 else 92318)
                batch_rows += cursor.count
                cursor.stream.close()
            count = check_union(paths, layer[batch], 23, 14, final=False)
            for path in paths+[layer[batch]]:
                assert sha(path) == frozen[str(path)]
            source_rows += batch_rows
            receipt = {"batch": batch, "first_original_run": first, "end_original_run_exclusive": end,
                       "input_run_count": len(paths), "input_rows": batch_rows, "unique_output_rows": count,
                       "every_input_row_and_stabilizer_independently_scanned": True,
                       "complete_exact_union_equal_retained_layer": True,
                       "retained_layer_sha256": sha(layer[batch])}
            receipts.append(receipt)
            ledger.write(json.dumps(receipt, separators=(",", ":"))+"\n")
            ledger.flush()
            print("N23/B14 fresh full original-run union batch", batch+1, "/25",
                  "input rows", batch_rows, "unique", count,
                  "seconds", round(time.monotonic()-started, 1), flush=True)
    assert source_rows == phase["rows_to_runs"]
    final_count = check_union(layer, target, 23, 14, final=True)
    assert final_count == header["orbits"]
    for path, digest in frozen.items():
        assert sha(path) == digest, ("bound source or input changed", path)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "independent-restored-N23-B14-all-retained-run-hierarchical-union-v1",
        "N": 23, "B": 14, "original_run_count": 779, "original_rows": source_rows,
        "layer0_batch_count": 25, "maximum_simultaneous_input_readers": 32,
        "all_779_original_runs_entirely_scanned_and_union_compared": True,
        "all_25_layer_inputs_entirely_compared_against_final_catalog": True,
        "all_row_masks_order_stabilizers_counts_and_end_of_file_checked": True,
        "every_hierarchical_batch_exact_complete_union_equality_verified": True,
        "all_original_and_intermediate_bytes_unchanged_after_acceptance": True,
        "residual_orbits": final_count, "catalog_sha256": sha(target),
        "catalog_relative_to_round4": target.relative_to(ROOT).as_posix(),
        "batch_receipts": receipts, "batch_receipts_sha256": sha(output / "BATCHES.jsonl"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "search_exhaustion_and_8726_historical_dependency_gates_not_accepted_here": True,
        "native_exhaustive_source_induction_and_actual_cover_transport_still_required": True,
        "all_residual_type_lower_bounds_not_paid_by_this_union": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 all-original hierarchical union independently accepted:", final_count,
          "residual types; native source gates and lower bounds still required", flush=True)


if __name__ == "__main__":
    main()
