"""Recover all original B14 runs, their retained first layer, and final proposal.

This is exact archive-byte materialization, not acceptance of native search,
union equality, pruned mathematics, or a competitor-family lower bound.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import json
import shutil
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from merge_paid_runs_bounded import phase_metadata

assert __debug__
PREFIX = "bulk/n23-B14-paid-search-stage-resume1/"
SOURCE_FILES = (
    "INPUT-BINDINGS.json", "N23-B14-pair-search.bin.building", "NATIVE-LAUNCH.json",
    "NATIVE-STDERR.log", "NATIVE-TERMINAL.json", "SEARCH-COMPLETE.json",
)
SELECTED = {PREFIX+name: "SOURCE/"+name for name in SOURCE_FILES}
SELECTED.update({
    PREFIX+f"N23-B14-pair-search.bin.runs/run-{i}.bin": f"RUNS/run-{i}.bin"
    for i in range(779)})
SELECTED.update({
    PREFIX+f"bounded-finalization/layer-0-batch-{i}.bin": f"LAYER0/batch-{i}.bin"
    for i in range(25)})
SELECTED[PREFIX+"bounded-finalization/RESIDUAL.bin"] = "FINAL/RESIDUAL.bin"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--observation", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    observationpath, output = args.observation.resolve(), args.output.resolve()
    assert observationpath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    observation = read(observationpath)
    assert observation["schema"] == "N23-B14-B15-family-archive-name-observation-v1"
    assert observation["source_sha256"] == sha(ROOT / "locate_n23_family_archive_assets.py")
    available = {}
    for row in observation["matching_members"]:
        if row["member"] not in SELECTED:
            continue
        assert row["member"] not in available
        available[row["member"]] = row
    assert len(SELECTED) == 811 and set(available) == set(SELECTED), (
        "missing exact original B14 union assets", sorted(set(SELECTED)-set(available))[:10])
    total = sum(row["bytes"] for row in available.values())
    assert total == 17915156184 and shutil.disk_usage(ROOT).free > total+20_000_000_000
    incoming = ROOT.parents[4]
    assert incoming.name == "_incoming-local-math-20261004"
    by_archive = defaultdict(list)
    for member, row in available.items():
        by_archive[row["archive"]].append(member)
    archive_bindings, expected = {}, {}
    for name in sorted(by_archive):
        archive = incoming / name
        metadata_path = incoming / (name+".meta.json")
        metadata = read(metadata_path)
        assert archive.stat().st_size == metadata["archive_bytes"]
        assert sha(archive) == metadata["sha256"]
        with zipfile.ZipFile(archive) as source:
            manifest = source.read("ASSET-MANIFEST.jsonl")
            for line in manifest.decode("utf8").splitlines():
                asset = json.loads(line, object_pairs_hook=no_duplicate_keys)
                member = asset["sourceRoot"]+"/"+asset["path"]
                if member in by_archive[name]:
                    assert member not in expected
                    expected[member] = asset
            for member in by_archive[name]:
                info = source.getinfo(member)
                assert info.file_size == available[member]["bytes"] == expected[member]["bytes"]
                assert info.CRC == available[member]["zip_crc32"]
        archive_bindings[name] = {
            "archive_sha256": metadata["sha256"], "metadata_sha256": sha(metadata_path),
            "asset_manifest_sha256": hashlib.sha256(manifest).hexdigest(),
        }
        print("Original B14 union source archive byte-checked:", name, flush=True)
    assert set(expected) == set(SELECTED)
    output.mkdir()
    publish(output / "INPUT-PLAN.json", {
        "schema": "isolated-N23-B14-811-union-asset-recovery-plan-v1",
        "N": 23, "B": 14, "original_runs": 779, "retained_first_layer_batches": 25,
        "total_uncompressed_bytes": total, "selected_members": SELECTED,
        "archive_bindings": archive_bindings,
        "old_final_file_is_only_an_unaccepted_union_proposal": True,
        "no_native_search_started_or_changed": True, "global_optimality_proved": False,
    })
    records = []
    copied_total = 0
    for name in sorted(by_archive):
        archive = incoming / name
        with zipfile.ZipFile(archive) as source:
            for member in sorted(by_archive[name]):
                target = (output / SELECTED[member]).resolve()
                assert target.is_relative_to(output) and not target.exists()
                target.parent.mkdir(parents=True, exist_ok=True)
                digest = hashlib.sha256()
                count = 0
                with source.open(member) as src, target.open("xb") as destination:
                    for block in iter(lambda: src.read(1 << 20), b""):
                        destination.write(block)
                        digest.update(block)
                        count += len(block)
                assert count == expected[member]["bytes"] and digest.hexdigest() == expected[member]["sha256"]
                assert sha(target) == expected[member]["sha256"]
                records.append({
                    "member": member, "recovered_file": SELECTED[member],
                    "bytes": count, "sha256": digest.hexdigest(),
                })
                copied_total += count
                if len(records) % 40 == 0 or member.endswith("/RESIDUAL.bin"):
                    print("Original B14 exact assets copied:", len(records), "/", len(SELECTED),
                          "bytes", copied_total, "/", total, flush=True)
        assert sha(archive) == archive_bindings[name]["archive_sha256"]
    assert copied_total == total and len(records) == 811
    source = output / "SOURCE"
    complete, terminal, launch, bindings = map(read, (
        source / "SEARCH-COMPLETE.json", source / "NATIVE-TERMINAL.json",
        source / "NATIVE-LAUNCH.json", source / "INPUT-BINDINGS.json"))
    phasepath = source / "N23-B14-pair-search.bin.building"
    phase = phase_metadata(phasepath)
    assert (phase["N"], phase["B"], phase["run_count"], phase["rows_to_runs"]) == (
        23, 14, 779, 77892318)
    assert phase["proof_prunes"] == 0 and phase["proof_payments"] == []
    assert complete["phase_sha256"] == sha(phasepath)
    assert complete["terminal_sha256"] == sha(source / "NATIVE-TERMINAL.json")
    assert complete["input_bindings_sha256"] == terminal["input_bindings_sha256"] == sha(
        source / "INPUT-BINDINGS.json")
    assert terminal["native_stderr_sha256"] == sha(source / "NATIVE-STDERR.log")
    assert terminal["native_pid"] == launch["native_pid"]
    assert terminal["native_terminal_observed"] and terminal["native_exit_code"] == 0
    assert complete["verified"] and complete["native_exhaustive_search_terminated_successfully"]
    assert not complete["unique_catalogue_finalized"]
    assert complete["old_prefix_runs_regenerated_and_compared"] == phase["prefix_runs_replayed_and_compared"] == 0
    assert (complete["N"], complete["B"], bindings["N"], bindings["B"]) == (23, 14, 23, 14)
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 23
    assert phase["scale"] == constants["angle_scale"] and phase["caps"] == constants["angle_caps"]
    assert complete["source_sha256"] == sha(HIGH / "enumerate_search_stage.py")
    frozen = {
        str(path): sha(path) for path in (
            Path(__file__).resolve(), observationpath, constants_path,
            HIGH / "enumerate_search_stage.py", HIGH / "merge_paid_runs_bounded.py",
            HIGH / "paid_binary_residual.py", output / "INPUT-PLAN.json")
    }
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "isolated-N23-B14-all-original-union-asset-byte-recovery-v1",
        "N": 23, "B": 14, "assets": records, "total_uncompressed_bytes": total,
        "archive_bindings": archive_bindings, "original_run_count": 779,
        "retained_layer0_batches": 25, "phase_rows_to_runs": 77892318,
        "all_assets_match_original_archive_manifest_crc_size_and_sha256": True,
        "historical_search_receipt_terminal_phase_and_bindings_byte_links_checked": True,
        "historical_source_phase_reports_no_paid_prunes": True,
        "old_native_pid_not_interpreted_as_a_current_process": True,
        "all_8726_old_absolute_launch_dependencies_not_restored_or_accepted_here": True,
        "actual_all_run_and_layer_union_equality_not_yet_accepted": True,
        "native_source_completeness_and_actual_cover_reduction_still_upstream": True,
        "not_a_lower_bound_payment": True, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("Original B14 union bytes recovered:", total,
          "bytes; fresh all-run/layer union equality and upstream source gates still required", flush=True)


if __name__ == "__main__":
    main()
