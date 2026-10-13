"""Complete n25/B15,16,17 necessary collar search with no proof pruning.

Native termination, canonical catalog acceptance, input immutability, and
source/control bindings are separate gates. No weak-graph lower bounds are
asserted by this cataloguing driver.
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
from test_sparse_collar import mechanical_derivation
from test_outer_collar import collar_codes, linux_path, WSL
from n25_outer_search import read, publish, bind, unchanged
from angle_obstructions import constants_gate

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--B", type=int, choices=(15, 16, 17), required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    B = args.B
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and output != ROOT and not output.exists()
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constants_gate(constants)
    assert [B, 25-B] in constants["families"]
    mechanical_derivation()
    controls = read(args.controls)
    assert controls["verified"] and controls["schema"] == "n25-family-no-payment-collar-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_family_collar.py")
    assert controls["native_source_sha256"] == sha(ROOT / "peel_sparse_outer_collar.cpp")
    assert controls["native_binary_sha256"] == sha(ROOT / "peel_sparse_outer_collar-linux")
    assert controls["frozen_degree_source_sha256"] == sha(HIGH / "peel_degree.cpp")
    assert controls["full_reference_binary_sha256"] == sha(HIGH / "peel_outer_stream.exe")
    assert controls["base_controls_sha256"] == sha(ROOT / "outer-collar-controls-v3-deep-internal/VERIFIED.json")
    assert controls["all_complete_reference_outer_restrictions_present"]
    assert controls["guards_disabled_complete_collar_sets_equal"]
    assert len(controls["cases"]) == 18
    assert set(controls["negative_controls_rejected"]) == {"node-limit", "bad-N", "bad-B"}
    files = {}
    for path in (
        Path(__file__), args.controls, constants_path, ROOT / "test_family_collar.py",
        ROOT / "angle_obstructions.py", ROOT / "SHORT-PATH-ANGLE-CERTIFICATES.md",
        ROOT / "test_outer_collar.py", ROOT / "test_sparse_collar.py", ROOT / "derive_sparse_collar.py",
        ROOT / "sparse-collar-source-derivation.json", ROOT / "peel_outer_collar.cpp",
        ROOT / "peel_sparse_outer_collar.cpp", ROOT / "peel_sparse_outer_collar-linux",
        ROOT / "sparse_outer_matcher.inc", HIGH / "paid_outer_matcher.inc", HIGH / "peel_degree.cpp",
        HIGH / "peel_outer_stream.exe", HIGH / "group_catalog.py", HIGH / "stream_catalog.py",
        ROOT / "OUTER-COLLAR-REDUCTION-DRAFT.md",
        ROOT / "outer-collar-controls-v3-deep-internal/VERIFIED.json",
    ):
        bind(files, path)
    output.mkdir()
    target = output / f"N25-B{B}-necessary-collars.json"
    relative = os.path.relpath(target, ROOT).replace("\\", "/")
    assert relative.isascii()
    command = [WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C",
               linux_path(ROOT), "./peel_sparse_outer_collar-linux", "25", str(B), relative,
               str(constants["angle_scale"]), *map(str, constants["angle_caps"]), "0", "dfs", "-", "-"]
    publish(output / "INPUT-BINDINGS.json", {
        "N": 25, "B": B, "command": command, "files_relative_to_workspace": files,
        "sparse_and_exact_proof_guards_disabled": True, "global_optimality_proved": False,
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
        print("N25/B", B, "full necessary collar search dispatched; WSL proxy", process.pid, flush=True)
        while True:
            try:
                code = process.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                if native_pid is None:
                    text = (output / "NATIVE-STDERR.log").read_text(encoding="utf8", errors="replace")
                    match = re.search(rf"COLLAR NATIVE PID=(\d+) N=25 B={B}", text)
                    if match:
                        native_pid = int(match.group(1))
                        publish(output / "LINUX-NATIVE-IDENTITY.json", {
                            "linux_native_pid": native_pid,
                            "binary_linux_path": linux_path(ROOT / "peel_sparse_outer_collar-linux"),
                            "native_binary_sha256": sha(ROOT / "peel_sparse_outer_collar-linux"),
                            "owned_wsl_proxy_pid": process.pid, "check_proc_identity_before_any_signal": True,
                        })
                        print("Actual native PID", native_pid, flush=True)
        collector.join(timeout=30)
        assert not collector.is_alive()
        process.stdout.close()
    text = (output / "NATIVE-STDERR.log").read_text(encoding="utf8", errors="replace")
    match = re.search(rf"COLLAR NATIVE PID=(\d+) N=25 B={B}", text)
    if match:
        native_pid = int(match.group(1))
    publish(output / "NATIVE-TERMINAL.json", {
        "native_terminal_observed": True, "actual_exit_code": code, "linux_native_pid": native_pid,
        "owned_wsl_proxy_pid": process.pid, "seconds": time.monotonic()-started,
        "native_log_sha256": sha(output / "NATIVE-STDERR.log"), "global_optimality_proved": False,
    })
    assert code == 0, "nonzero/memory-limited run is not a complete catalog"
    unchanged(files)
    header, codes = collar_codes(target, 25, B)
    assert header["mode"] == "dfs" and header["screen"]
    assert header["scale"] == constants["angle_scale"] and header["caps"] == constants["angle_caps"]
    assert header["sparse_patterns_loaded"] == header["paid_patterns_loaded"] == 0
    assert header["sparse_proof_prunes"] == header["proof_prunes"] == 0
    groups = [{"id": gid, **row, "members": 1} for gid, row in enumerate(header["weak_graphs"])]
    bindings = output / "bindings.jsonl"
    with bindings.open("x", encoding="utf8") as stream:
        for group in groups:
            stream.write(json.dumps({
                "index": group["id"], "group": group["id"],
                "map": {"centers": list(range(group["centers"])), "anchors": list(range(B)),
                        "orientation": 1, "shift": 0},
            }, separators=(",", ":"))+"\n")
    publish(output / "GROUPS.json", {
        "N": 25, "B": B, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups), "catalog_sha256": sha(target),
        "bindings_file": bindings.name, "bindings_sha256": sha(bindings),
        "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": True,
        "parent_groups_sha256": None, "parent_proof_sha256": None,
        "source_sha256": sha(Path(__file__)), "members_are_necessary_weak_graphs_not_full_types": True,
        "global_optimality_proved": False,
    })
    unchanged(files)
    publish(output / "SUMMARY.json", {
        "verified": True, "N": 25, "B": B, "complete_necessary_outer_collar_overapproximation": True,
        "unpaid_weak_graphs": len(groups), "all_remaining_weak_lower_bounds_paid": len(groups) == 0,
        "full_triangulations_not_enumerated": True, "source_induction_required_for_cover_transport": True,
        "native_catalog_sha256": sha(target), "groups_sha256": sha(output / "GROUPS.json"),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("N25/B", B, "complete necessary catalog accepted:", len(groups), "unpaid weak graphs", flush=True)


if __name__ == "__main__":
    main()
