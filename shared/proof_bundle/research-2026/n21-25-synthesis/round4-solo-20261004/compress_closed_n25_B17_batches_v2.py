"""All logical files pre/post compared for transparent completed-proof storage.

The stopped v1 is retained and has no acceptance. This successor checks every
file, including logs and pending families, not just shared worker bindings.
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


def compact(target, output, label, recursive):
    target = target.resolve()
    assert target == STAGE or (target.parent == STAGE and target.name.startswith("batch-"))
    assert target.is_dir() and target.is_relative_to(ROOT)
    for entry in target.rglob("*") if recursive else [target]:
        assert not entry.stat(follow_symlinks=False).st_file_attributes & 0x400
    command = ["compact.exe", "/C", "/I", "/Q"]
    command += ["/S:"+str(target), "*"] if recursive else [str(target)]
    result = subprocess.run(command, cwd=str(target), capture_output=True,
                            creationflags=subprocess.CREATE_NO_WINDOW)
    with (output / (label+"-STDOUT.log")).open("xb") as stream:
        stream.write(result.stdout)
    with (output / (label+"-STDERR.log")).open("xb") as stream:
        stream.write(result.stderr)
    publish(output / (label+"-TERMINAL.json"), {
        "actual_exit_code": result.returncode, "actual_process_terminal_observed": True,
        "actual_target": str(target), "recursive_actual_closed_batch_only": recursive,
        "source_sha256": sha(Path(__file__)), "not_a_mathematical_payment": True})
    return result.returncode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert os.name == "nt" and output.is_relative_to(ROOT) and not output.exists()
    assert STAGE.resolve().parent == ROOT
    scoped, seen = [], set()
    with (STAGE / "COMPLETED-BATCHES.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            if not line.endswith("\n"):
                break
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            first = descriptor["first"]
            assert type(first) is int and first >= 0 and first % 128 == 0 and first not in seen
            seen.add(first)
            directory = STAGE / f"batch-{first//128:06}"
            assert sha(directory / "SUMMARY.json") == descriptor["worker_report_sha256"]
            scoped.append((directory, descriptor))
    assert scoped
    output.mkdir()
    freebefore = shutil.disk_usage(ROOT).free
    rootinput = STAGE / "INPUT-BINDINGS.json"
    rootdigest = sha(rootinput)
    rootcode = compact(STAGE, output, "FUTURE-DIRECTORY-ATTRIBUTE", False)
    assert sha(rootinput) == rootdigest
    results, checked, errors = [], 0, []
    for directory, descriptor in sorted(scoped, key=lambda item: str(item[0])):
        worker = read(directory / "SUMMARY.json")
        assert worker["schema"] == "complete-parent-pending-filling-worker-v1"
        assert (worker["N"], worker["B"], worker["first"], worker["count"]) == (
            25, 17, descriptor["first"], descriptor["count"])
        for row in worker["outcomes"]:
            if row["status"] == "strict-complete-filling-family":
                for field, digestfield in (("proof_relative_to_stage", "proof_sha256"),
                                            ("exact_relative_to_stage", "exact_sha256")):
                    path = (directory / row[field]).resolve()
                    assert path.is_relative_to(directory) and sha(path) == row[digestfield]
        # Snapshot every actual file, not only the shared-source frozen list.
        files = sorted(path for path in directory.rglob("*") if path.is_file())
        assert files
        before = {path: sha(path) for path in files}
        assert before[directory / "SUMMARY.json"] == descriptor["worker_report_sha256"]
        code = compact(directory, output, directory.name, True)
        afterfiles = sorted(path for path in directory.rglob("*") if path.is_file())
        assert afterfiles == files, "closed evidence filenames changed during storage operation"
        differences = [str(path) for path in files if sha(path) != before[path]]
        assert not differences, ("actual proof or other closed-batch logical bytes changed", differences)
        checked += len(files)
        if code:
            errors.append(directory.name)
        results.append({
            "batch": descriptor["first"]//128, "actual_compression_exit": code,
            "original_worker_summary_sha256": descriptor["worker_report_sha256"],
            "every_actual_file_pre_and_post_sha256_compared": len(files),
            "logical_byte_differences": differences})
        if len(results) % 5 == 0:
            print("B17 ended proof storage: ALL actual files byte-compared",
                  len(results), "/", len(scoped), "files", checked,
                  "differences 0; free bytes", shutil.disk_usage(ROOT).free, flush=True)
    publish(output / "VERIFIED-STORAGE.json", {
        "storage_only_verified": True, "N": 25, "B": 17,
        "every_actual_closed_batch_file_logical_bytes_pre_and_post_compared": True,
        "all_actual_file_sets_and_all_logical_bytes_unchanged": True,
        "original_positive_proof_and_exact_hashes_also_checked_before_storage_operation": True,
        "only_actual_ended_descriptor_batches_recursively_compressed": True,
        "future_directory_compression_attribute_exit": rootcode,
        "original_unfinished_workers_not_restarted_or_sources_modified": True,
        "scoped_ended_batches": len(scoped), "all_actual_files_byte_compared": checked,
        "results": results, "compression_error_batches_not_claimed_fully_compressed": errors,
        "free_bytes_before": freebefore, "free_bytes_after": shutil.disk_usage(ROOT).free,
        "no_proof_files_deleted_or_moved": True,
        "storage_metadata_reversible_original_paths_and_all_logical_bytes_preserved": True,
        "v1_not_used_as_all_actual_proof_byte_acceptance": True,
        "source_sha256": sha(Path(__file__)),
        "not_a_mathematical_source_lower_payment_or_global_acceptance": True})
    print("Transparent ended proof storage full-file pre/post byte comparison finished;",
          "not a mathematical acceptance", flush=True)


if __name__ == "__main__":
    main()
