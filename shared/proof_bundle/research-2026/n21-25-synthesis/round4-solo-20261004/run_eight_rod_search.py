"""Fresh n25 necessary search with eight-rod angles and strict sparse guards.

Source induction, exact angle-cap acceptance, graph-theorem acceptance,
injection controls, complete partition controls, native exhaustion, immutable
bindings, and canonical catalog checks remain distinct obligations.
"""
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate
from n25_outer_search import read, bind, unchanged, publish
from verify_sparse_maps_fast import library_gate
from eight_rod_angles import constants_gate, CAP8
from test_eight_rod_collar import derivation_gate
from test_outer_collar import collar_codes, linux_path, WSL

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--maps", type=Path, required=True)
    ap.add_argument("--eight-controls", type=Path, required=True)
    ap.add_argument("--guard-controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and output != ROOT and not output.exists()
    constants, library, table, files = library_gate(args.library.resolve())
    B = library["B"]
    constants_gate(constants)
    derivation_gate()
    maps, eight, guard = map(read, (args.maps, args.eight_controls, args.guard_controls))
    assert maps["verified"] and maps["schema"] == "fresh-sparse-library-explicit-map-controls-v1"
    assert maps["B"] == B and maps["library_sha256"] == sha(args.library)
    assert maps["source_sha256"] == sha(ROOT / "verify_sparse_maps_fast.py")
    assert maps["matcher_include_sha256"] == sha(ROOT / "sparse_outer_matcher.inc")
    assert maps["matcher_binary_sha256"] == sha(ROOT / "sparse_outer_match-linux")
    assert maps["all_source_trees_fresh_exact_replayed"] and maps["explicitly_checked_native_maps"] > 0
    assert maps["independent_python_existence_controls"] > 0
    assert set(maps["negative_controls_rejected"]) == {"wrong-anchor-offset", "center-collision", "missing-image-face"}
    if B == 16:
        assert maps["known_B16_attaining_graph_not_matched"]
    assert eight["verified"] and eight["schema"] == "eight-rod-collar-controls-v1"
    assert eight["source_sha256"] == sha(ROOT / "test_eight_rod_collar.py")
    assert eight["native_source_sha256"] == sha(ROOT / "peel_eight_rod_collar.cpp")
    assert eight["native_binary_sha256"] == sha(ROOT / "peel_eight_rod_collar-linux")
    assert eight["native_angle_source_sha256"] == sha(ROOT / "eight_rod_possible.inc")
    assert eight["independent_cycle_checker_sha256"] == sha(ROOT / "eight_rod_angles.py")
    assert eight["cap_report_sha256"] == sha(ROOT / "n25-eight-rod-exact-cap-20261005-v1.json")
    assert eight["native_results_agree_with_independent_exact_cycles"]
    assert eight["all_four_exact_attaining_controls_retained"]
    assert eight["additional_exclusions_beyond_old_angles"] > 0
    assert len(eight["no_screen_complete_controls"]) == 18
    assert len(eight["complete_screened_reference_controls"]) == 2
    assert set(eight["negative_controls_rejected"]) == {
        "wrong-weight", "broken-cycle", "too-long-path", "node-limit", "bad-N", "bad-B", "bad-cap8"}
    assert guard["verified"] and guard["schema"] == "eight-rod-sparse-complete-partition-controls-v1"
    assert guard["B"] == B and guard["library_sha256"] == sha(args.library)
    assert guard["source_sha256"] == sha(ROOT / "test_eight_sparse_guard.py")
    assert guard["maps_controls_sha256"] == sha(args.maps)
    assert guard["eight_controls_sha256"] == sha(args.eight_controls)
    assert guard["native_source_sha256"] == sha(ROOT / "peel_eight_rod_collar.cpp")
    assert guard["native_binary_sha256"] == sha(ROOT / "peel_eight_rod_collar-linux")
    assert guard["sparse_guard_sha256"] == sha(ROOT / "sparse_outer_matcher.inc")
    assert guard["all_baseline_minus_residual_graphs_individually_paid"]
    assert len(guard["cases"]) == 4
    assert all(row["all_removed_weak_graphs_explicitly_paid"] for row in guard["cases"])
    assert set(guard["negative_controls_rejected"]) == {"node-limit", "bad-N", "bad-B"}
    files.update(maps["files_relative_to_workspace"])
    files.update(guard["files_relative_to_workspace"])
    for path in (
        Path(__file__), args.library, args.maps, args.eight_controls, args.guard_controls,
        ROOT / "verify_sparse_maps_fast.py", ROOT / "family_sparse_gate.py",
        ROOT / "run_sparse_collar.py", ROOT / "test_eight_sparse_guard.py",
        ROOT / "test_eight_rod_collar.py", ROOT / "eight_rod_angles.py",
        ROOT / "eight_rod_possible.inc", ROOT / "peel_eight_rod_collar.cpp",
        ROOT / "peel_eight_rod_collar-linux", ROOT / "derive_eight_rod_collar.py",
        ROOT / "eight-rod-collar-source-derivation.json",
        ROOT / "n25-eight-rod-exact-cap-20261005-v1.json",
        ROOT / "test_eight_possible.cpp", ROOT / "test_eight_possible-linux",
        ROOT / "eight_collar_probe_body.inc", ROOT / "derive_eight_possible_test.py",
        ROOT / "eight-possible-test-source-derivation.json",
        ROOT / "sparse_outer_matcher.inc", ROOT / "sparse_outer_match.cpp", ROOT / "sparse_outer_match-linux",
        ROOT / "EIGHT-ROD-ANGLE-SOURCE.md", ROOT / "N25-COLLAR-COVER-INTERFACE.md",
        ROOT / "SPARSE-OUTER-OBSTACLE-TRANSPORT.md", ROOT / "OUTER-COLLAR-REDUCTION-DRAFT.md",
        HIGH / "peel_degree.cpp", HIGH / "paid_outer_matcher.inc",
        HIGH / "group_catalog.py", HIGH / "stream_catalog.py",
    ):
        bind(files, path)
    unchanged(files)
    output.mkdir()
    target = output / f"N25-B{B}-necessary-eight-rod-collars.json"
    relative = lambda path: os.path.relpath(path, ROOT).replace("\\", "/")
    assert relative(target).isascii() and relative(table).isascii()
    command = [
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./peel_eight_rod_collar-linux", "25", str(B), relative(target),
        str(constants["angle_scale"]), *map(str, constants["angle_caps"]),
        "0", "dfs", "-", relative(table), str(CAP8),
    ]
    publish(output / "INPUT-BINDINGS.json", {
        "N": 25, "B": B, "command": command, "files_relative_to_workspace": files,
        "cap8": CAP8, "same_non_omitted_recursion_and_sparse_injection_checks": True,
        "global_optimality_proved": False,
    })
    started, native_pid = time.monotonic(), None
    with (output / "NATIVE-STDERR.log").open("xb") as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        def collect():
            for chunk in iter(process.stdout.readline, b""):
                log.write(chunk)
                log.flush()
        collector = threading.Thread(target=collect, daemon=True)
        collector.start()
        publish(output / "WSL-LAUNCH.json", {"owned_wsl_proxy_pid": process.pid, "command": command})
        print("N25/B", B, "eight-rod necessary search dispatched; WSL proxy", process.pid, flush=True)
        while True:
            try:
                code = process.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                if native_pid is None:
                    text = (output / "NATIVE-STDERR.log").read_text(encoding="utf8", errors="replace")
                    match = re.search(rf"EIGHT ROD NATIVE PID=(\d+) N=25 B={B}", text)
                    if match:
                        native_pid = int(match.group(1))
                        publish(output / "LINUX-NATIVE-IDENTITY.json", {
                            "linux_native_pid": native_pid,
                            "binary_linux_path": linux_path(ROOT / "peel_eight_rod_collar-linux"),
                            "native_binary_sha256": sha(ROOT / "peel_eight_rod_collar-linux"),
                            "owned_wsl_proxy_pid": process.pid, "check_proc_identity_before_any_signal": True,
                        })
                        print("Actual eight-rod native PID", native_pid, flush=True)
        collector.join(timeout=30)
        assert not collector.is_alive()
        process.stdout.close()
    text = (output / "NATIVE-STDERR.log").read_text(encoding="utf8", errors="replace")
    match = re.search(rf"EIGHT ROD NATIVE PID=(\d+) N=25 B={B}", text)
    if match:
        native_pid = int(match.group(1))
    publish(output / "NATIVE-TERMINAL.json", {
        "native_terminal_observed": True, "actual_exit_code": code, "linux_native_pid": native_pid,
        "owned_wsl_proxy_pid": process.pid, "seconds": time.monotonic()-started,
        "native_log_sha256": sha(output / "NATIVE-STDERR.log"), "global_optimality_proved": False,
    })
    assert code == 0, "nonzero, memory- or node-limited run is not a complete necessary catalog"
    unchanged(files)
    header, codes = collar_codes(target, 25, B)
    assert header["mode"] == "dfs" and header["screen"] and header["eight_rod_screen"]
    assert header["cap8"] == CAP8 and header["scale"] == constants["angle_scale"]
    assert header["caps"] == constants["angle_caps"]
    assert header["sparse_patterns_loaded"] == library["obstacle_count"] and header["paid_patterns_loaded"] == 0
    byid = {o["id"]: o for o in library["obstacles"]}
    for payment in header["sparse_payments"]:
        mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
        validate(25, B, byid[payment["obstacle"]]["faces"], mapping, payment["sample_faces"])
    groups = [{"id": gid, **row, "members": 1} for gid, row in enumerate(header["weak_graphs"])]
    bindings = output / "bindings.jsonl"
    with bindings.open("x", encoding="utf8") as stream:
        for row in groups:
            stream.write(json.dumps({
                "index": row["id"], "group": row["id"],
                "map": {"centers": list(range(row["centers"])), "anchors": list(range(B)),
                        "orientation": 1, "shift": 0},
            }, separators=(",", ":"))+"\n")
    publish(output / "GROUPS.json", {
        "N": 25, "B": B, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups), "catalog_sha256": sha(target),
        "bindings_file": bindings.name, "bindings_sha256": sha(bindings),
        "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": True,
        "parent_groups_sha256": None, "parent_proof_sha256": None,
        "members_are_necessary_weak_graphs_not_full_types": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    unchanged(files)
    publish(output / "SUMMARY.json", {
        "verified": True, "N": 25, "B": B, "complete_necessary_outer_collar_overapproximation": True,
        "unpaid_weak_graphs": len(groups), "all_remaining_weak_lower_bounds_paid": len(groups) == 0,
        "full_triangulations_not_enumerated": True, "source_induction_required_for_cover_transport": True,
        "cap8": CAP8, "native_catalog_sha256": sha(target), "groups_sha256": sha(output / "GROUPS.json"),
        "payment_samples_explicitly_mapped": len(header["sparse_payments"]),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("N25/B", B, "complete eight-rod necessary catalog accepted:", len(groups), "unpaid weak graphs", flush=True)


if __name__ == "__main__":
    main()
