"""Transparent NTFS storage only: finished batches, original proof bytes checked.

This is neither a mathematical accepter nor an edit of a running proof source.
No file is removed, renamed, archived, or rewritten at the logical-byte level.
"""
from pathlib import Path
import argparse
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
STAGE = ROOT / "n25-B17-f1"
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish

assert __debug__


def compress(target, output, label, recursive):
    target = target.resolve()
    assert target == STAGE or (target.parent == STAGE and target.name.startswith("batch-"))
    assert target.is_dir() and target.is_relative_to(ROOT)
    entries = target.rglob("*") if recursive else [target]
    for entry in entries:
        assert not entry.stat(follow_symlinks=False).st_file_attributes & 0x400, (
            "reparse point would escape the intended transparent-storage target", entry)
    command = ["compact.exe", "/C", "/I", "/Q"]
    if recursive:
        command.extend(["/S:"+str(target), "*"])
    else:
        command.append(str(target))
    result = subprocess.run(command, cwd=str(target), capture_output=True,
                            creationflags=subprocess.CREATE_NO_WINDOW)
    with (output / (label+"-STDOUT.log")).open("xb") as stream:
        stream.write(result.stdout)
    with (output / (label+"-STDERR.log")).open("xb") as stream:
        stream.write(result.stderr)
    publish(output / (label+"-TERMINAL.json"), {
        "actual_exit_code": result.returncode, "actual_process_terminal_observed": True,
        "actual_target": str(target), "recursive_closed_batch_only": recursive,
        "command": command, "source_sha256": sha(Path(__file__)),
        "not_a_mathematical_payment": True})
    return result.returncode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert os.name == "nt" and output.is_relative_to(ROOT) and not output.exists()
    assert STAGE.resolve().parent == ROOT
    descriptors = []
    with (STAGE / "COMPLETED-BATCHES.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            if not line.endswith("\n"):
                break
            descriptors.append(json.loads(line, object_pairs_hook=no_duplicate_keys))
    assert descriptors
    seen, scoped = set(), []
    for descriptor in descriptors:
        first = descriptor["first"]
        assert type(first) is int and first >= 0 and first % 128 == 0 and first not in seen
        seen.add(first)
        directory = STAGE / f"batch-{first//128:06}"
        assert sha(directory / "SUMMARY.json") == descriptor["worker_report_sha256"]
        scoped.append((directory, descriptor))
    output.mkdir()
    freebefore = shutil.disk_usage(ROOT).free
    rootinput = STAGE / "INPUT-BINDINGS.json"
    rootdigest = sha(rootinput)
    rootcode = compress(STAGE, output, "FUTURE-DIRECTORY-ATTRIBUTE", False)
    assert sha(rootinput) == rootdigest
    results, checked, errors = [], 0, []
    for directory, descriptor in sorted(scoped, key=lambda item: str(item[0])):
        before = descriptor["worker_report_sha256"]
        worker = read(directory / "SUMMARY.json")
        assert worker["schema"] == "complete-parent-pending-filling-worker-v1"
        assert (worker["N"], worker["B"], worker["first"], worker["count"]) == (
            25, 17, descriptor["first"], descriptor["count"])
        code = compress(directory, output, directory.name, True)
        differences, count = [], 0
        for name, expected in worker["frozen_files"].items():
            path = Path(name).resolve()
            if not path.is_relative_to(directory):
                continue
            if sha(path) != expected:
                differences.append(str(path))
            count += 1
        assert sha(directory / "SUMMARY.json") == before
        assert not differences, ("finished proof logical bytes differ from original frozen identity", differences)
        checked += count
        if code:
            errors.append(directory.name)
        results.append({
            "batch": descriptor["first"]//128, "actual_compression_exit": code,
            "original_worker_summary_sha256": before, "bound_proof_inputs_byte_checked": count,
            "logical_byte_differences": differences})
        if len(results) % 5 == 0:
            print("Finished B17 proof storage compression and frozen-byte check",
                  len(results), "/", len(scoped), "bound inputs", checked,
                  "byte differences 0; current free bytes", shutil.disk_usage(ROOT).free, flush=True)
    publish(output / "VERIFIED-STORAGE.json", {
        "storage_only_verified": True, "N": 25, "B": 17,
        "original_logical_proof_bytes_and_worker_summaries_unchanged": True,
        "only_actual_ended_descriptor_batches_recursively_compressed": True,
        "future_stage_directory_compression_attribute_exit": rootcode,
        "original_unfinished_workers_not_restarted_or_sources_modified": True,
        "scoped_ended_batches": len(scoped), "bound_proof_input_files_checked": checked,
        "results": results, "compression_error_batches_not_falsely_claimed_compressed": errors,
        "free_bytes_before": freebefore, "free_bytes_after": shutil.disk_usage(ROOT).free,
        "no_proof_files_deleted_or_moved": True,
        "NTFS_storage_metadata_reversible_with_logical_content_and_original_paths_preserved": True,
        "source_sha256": sha(Path(__file__)),
        "not_a_mathematical_source_or_lower_payment_or_global_acceptance": True})
    print("Transparent completed-proof storage step finished; logical frozen bytes unchanged;",
          "not a mathematical acceptance", flush=True)


if __name__ == "__main__":
    main()
