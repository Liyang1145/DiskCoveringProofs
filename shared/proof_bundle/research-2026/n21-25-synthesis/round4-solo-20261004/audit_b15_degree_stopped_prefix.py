"""Preserve/hash the actual stopped B15 prefix; never certifies exhaustion."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from closed_origin_slab import rows

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    previous = ROOT / "n25-B15-origin-streamed-search-reboot-20261005-v1"
    record = ROOT / "n25-B15-controlled-degree-replacement-20261005-v1"
    pre, signal, terminal, inputs = map(read, (
        record / "PRE-SIGNAL.json", record / "SIGNAL-RESULT.json",
        previous / "NATIVE-TERMINAL.json", previous / "INPUT-BINDINGS.json"))
    assert pre["source_sha256"] == sha(ROOT / "b15_degree_controlled_stop.py")
    assert pre["old_search_relative_to_workspace"] == previous.name
    assert pre["owned_process_identity_independently_checked"]
    assert signal["exact_owned_native_SIGTERM_sent"] and signal["signal_command_exit_code"] == 0
    assert signal["linux_native_pid"] == pre["linux_native_pid"] == terminal["linux_native_pid"]
    assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] != 0
    assert terminal["owned_wsl_proxy_pid"] == pre["owned_wsl_proxy_pid"]
    assert terminal["manifest_sha256"] is None
    assert sha(previous / "NATIVE-STDERR.log") == terminal["native_log_sha256"]
    assert sha(previous / "INPUT-BINDINGS.json") == pre["old_input_bindings_sha256"]
    assert sha(previous / "LINUX-NATIVE-IDENTITY.json") == pre["old_native_identity_sha256"]
    assert (inputs["N"], inputs["B"]) == (25, 15)
    assert not (previous / "SUMMARY.json").exists()
    manifest = previous / "N25-B15-complete-origin-sorted-chunks.json"
    assert not manifest.exists()
    files = dict(inputs["files_relative_to_workspace"])
    unchanged(files)
    chunks = []
    for path in sorted(previous.glob(manifest.name+".chunk-*.jsonl")):
        index = int(path.name.split(".chunk-")[-1].split(".")[0])
        assert index == len(chunks)
        digest, count = sha(path), 0
        try:
            for row_index, _ in rows(path, 15, index):
                assert row_index == count
                count += 1
        except (AssertionError, ValueError, OSError) as error:
            # Preserve a possible interrupted last write but do not pay it.
            outcome = {
                "index": index, "file": path.name, "sha256": digest,
                "eligible_closed_100000_row_slab": False,
                "complete_rows_observed_before_rejection_not_payments": count,
                "rejection_class": type(error).__name__,
            }
        else:
            assert count == 100000
            outcome = {"index": index, "file": path.name, "sha256": digest,
                       "eligible_closed_100000_row_slab": True, "rows": count}
        assert sha(path) == digest
        chunks.append(outcome)
        bind(files, path)
    assert chunks
    for path in (Path(__file__), record / "PRE-SIGNAL.json", record / "SIGNAL-RESULT.json",
                 previous / "NATIVE-TERMINAL.json", previous / "NATIVE-STDERR.log",
                 previous / "INPUT-BINDINGS.json", previous / "LINUX-NATIVE-IDENTITY.json",
                 ROOT / "closed_origin_slab.py", ROOT / "b15_degree_controlled_stop.py"):
        bind(files, path)
    unchanged(files)
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "actual-controlled-stop-B15-finite-prefix-preservation-v1",
        "N": 25, "B": 15, "actual_native_exit_code": terminal["actual_exit_code"],
        "actual_wrapper_terminal_collected_separately": True, "old_prefix_files": chunks,
        "all_closed_chunks_full_syntax_and_order_scanned_not_proof_paid": True,
        "all_old_files_preserved_and_frozen_after_actual_stop": True,
        "in_memory_unflushed_rows_not_a_resumable_point": True,
        "not_a_complete_competitor_family_or_union": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("Stopped B15 prefix preserved:",
          sum(row["eligible_closed_100000_row_slab"] for row in chunks),
          "fully scanned closed slabs; actual exit", terminal["actual_exit_code"],
          "; not complete search", flush=True)


if __name__ == "__main__":
    main()
