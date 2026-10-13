"""New complete small-order outer-family search with a hard 4GiB slab guard."""
from pathlib import Path
import argparse
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from small_order_origin_caps import parameters
from test_outer_collar import WSL, linux_path

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, choices=(23, 24), required=True)
    ap.add_argument("--B", type=int, required=True)
    for name in ("controls", "caps", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    controlpath, cappath, output = (
        getattr(args, name).resolve() for name in ("controls", "caps", "output"))
    assert all(path.is_relative_to(ROOT) for path in (controlpath, cappath, output))
    assert not output.exists()
    assert shutil.disk_usage(ROOT).free >= 14*1024**3, "insufficient reserved space for bounded slabs+union"
    controls, caps_report = read(controlpath), read(cappath)
    assert controls["verified"] and controls["schema"] == "small-order-origin-collar-complete-source-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_small_order_origin_collar.py")
    assert controls["all_original_recursive_and_canonical_branches_literally_unchanged"]
    assert controls["both_N23_N24_true_attaining_graphs_retained_by_origin_and_own_angles"]
    assert caps_report["verified"] and caps_report["source_sha256"] == sha(ROOT / "small_order_origin_caps.py")
    constants, cap8, cap_record = parameters(args.n)
    assert [args.B, args.n-args.B] in constants["families"]
    assert cap_record == next(row for row in caps_report["orders"] if row["N"] == args.n)
    frozen = dict(controls["frozen_files"])
    necessitypath = ROOT / "n23-n24-cover-origin-necessity-controls-20261005-v1/VERIFIED.json"
    necessity = read(necessitypath)
    assert necessity["verified"] and necessity["source_sha256"] == sha(ROOT / "test_small_order_cover_origin.py")
    for relative, digest in necessity["files_relative_to_workspace"].items():
        path = (ROOT.parents[2] / relative).resolve()
        assert path.is_relative_to(ROOT.parents[2]) and sha(path) == digest
        assert str(path) not in frozen or frozen[str(path)] == digest
        frozen[str(path)] = digest
    for path in (Path(__file__), controlpath, cappath, necessitypath,
                 ROOT / "audit_small_order_origin_union.py", ROOT / "small_order_origin_caps.py",
                 ROOT.parent / f"evidence/core-reduction/constants/n{args.n}.json",
                 ROOT / "OUTER-COLLAR-REDUCTION-DRAFT.md", ROOT / "N23-N24-UNEXPOSED-ORIGIN-SOURCE.md",
                 HIGH / "group_catalog.py", HIGH / "audit_streamed_hierarchy.py",
                 ROOT / "merge_small_order_origin_chunks.py", Path(shutil.__file__)):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    manifestpath = output / "MANIFEST.json"
    relative = os.path.relpath(manifestpath, ROOT).replace("\\", "/")
    assert relative.isascii()
    command = list(map(str, [
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./peel_small_order_origin_collar-linux", args.n, args.B, relative, constants["angle_scale"],
        *constants["angle_caps"], 0, "dfs", "-", "-", cap8, 100000, 1]))
    publish(output / "INPUT-BINDINGS.json", {
        "N": args.n, "B": args.B, "command": command, "frozen_files": frozen,
        "controls_sha256": sha(controlpath), "caps_report_sha256": sha(cappath),
        "source_not_restricted_to_a_seed_or_discovery_sample": True,
        "original_sources_and_existing_proof_jobs_not_edited": True,
        "hard_native_sorted_slab_guard_bytes": 4*1024**3,
        "minimum_starting_free_bytes": 14*1024**3,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    logpath = output / "NATIVE-STDOUT-STDERR.log"
    started = time.monotonic()
    with logpath.open("xb") as log:
        process = subprocess.Popen(command, cwd=str(ROOT), stdout=log, stderr=log,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        publish(output / "NATIVE-LAUNCH.json", {
            "windows_native_launcher_pid": process.pid, "command": command,
            "input_bindings_sha256": sha(output / "INPUT-BINDINGS.json"),
            "native_terminal_observed": False,
        })
        print("New small-order complete outer search launched:", args.n, args.B,
              "Windows launcher", process.pid, "; independent union only after real exit0", flush=True)
        code = process.wait()
    logtext = logpath.read_text(encoding="utf8", errors="replace")
    matches = re.findall(r"COVER ORIGIN NATIVE PID=(\d+) N=(\d+) B=(\d+)", logtext)
    publish(output / "NATIVE-TERMINAL.json", {
        "windows_native_launcher_pid": process.pid, "command": command,
        "actual_exit_code": code, "native_terminal_observed": True,
        "native_linux_identity_line": matches,
        "input_bindings_sha256": sha(output / "INPUT-BINDINGS.json"),
        "native_log_sha256": sha(logpath), "manifest_sha256": sha(manifestpath) if manifestpath.exists() else None,
        "seconds": time.monotonic()-started, "source_sha256": sha(Path(__file__)),
    })
    assert code == 0 and len(matches) == 1
    assert matches[0][1:] == (str(args.n), str(args.B))
    for path, digest in frozen.items():
        assert sha(path) == digest
    auditor = ROOT / "audit_small_order_origin_union.py"
    with (output / "UNION-STDOUT.log").open("xb") as stdout, \
            (output / "UNION-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(list(map(str, [
            sys.executable, "-u", auditor, "--stage", output, "--controls", controlpath,
            "--caps", cappath, "--output", output / "ACCEPTED"])),
            cwd=str(ROOT), stdout=stdout, stderr=stderr,
            creationflags=subprocess.CREATE_NO_WINDOW)
        code = process.wait()
    publish(output / "UNION-TERMINAL.json", {
        "child_pid": process.pid, "actual_exit_code": code,
        "independent_process_terminal_observed": True, "audit_source_sha256": sha(auditor),
    })
    assert code == 0
    for path, digest in frozen.items():
        assert sha(path) == digest
    result = read(output / "ACCEPTED/SOURCE-ACCEPTED.json")
    assert result["verified"]
    publish(output / "PIPELINE-COMPLETED.json", {
        "N": args.n, "B": args.B, "actual_native_and_union_terminals_observed": True,
        "source_acceptance_sha256": sha(output / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("New small-order complete outer family source+union pipeline accepted; lower payments still owed",
          flush=True)


if __name__ == "__main__":
    main()
