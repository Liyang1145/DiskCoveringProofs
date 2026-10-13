"""Derived generic-B strict collar production driver; no old inputs edited."""
from pathlib import Path
from fractions import Fraction as F
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
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate
from test_outer_collar import linux_path, WSL, collar_codes
from test_sparse_collar import mechanical_derivation
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
assert __debug__

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--maps", type=Path, required=True)
    args = ap.parse_args()
    B = read(args.library)["B"]
    assert B == 15
    output = args.output.resolve()
    assert output.is_relative_to(ROOT.resolve()) and output != ROOT.resolve() and not output.exists()
    constants, library, table, files = sparse_library_gate(args.library.resolve())
    mechanical_derivation()
    controls = read(args.controls)
    assert controls["verified"] and controls["library_sha256"] == sha(args.library)
    assert controls["source_sha256"] == sha(ROOT / "test_generic_sparse_collar.py")
    assert controls["native_source_sha256"] == sha(ROOT / "peel_sparse_outer_collar.cpp")
    assert controls["native_binary_sha256"] == sha(ROOT / "peel_sparse_outer_collar-linux")
    assert controls["sparse_guard_sha256"] == sha(ROOT / "sparse_outer_matcher.inc")
    assert controls["all_baseline_minus_residual_graphs_independently_paid"] and controls["no_sparse_guard_full_set_equal"]
    assert len(controls["cases"]) == 10 and set(controls["negative_controls_rejected"]) == {"node-limit", "bad-N", "bad-B"}
    maps_path = args.maps.resolve()
    maps = read(maps_path)
    assert sha(maps_path) == controls["proper_matching_controls_sha256"]
    assert maps["verified"] and maps["library_sha256"] == sha(args.library)
    assert maps["matcher_include_sha256"] == sha(ROOT / "sparse_outer_matcher.inc")
    basepath = ROOT / "outer-collar-controls-v3-deep-internal/VERIFIED.json"
    base = read(basepath)
    assert base["verified"] and base["all_full_reference_outer_restrictions_present"]
    assert base["native_source_sha256"] == sha(ROOT / "peel_outer_collar.cpp")
    assert base["frozen_degree_source_sha256"] == sha(HIGH / "peel_degree.cpp")
    assert len(base["cases"]) == 18
    for p in (
        args.controls, ROOT / "test_generic_sparse_collar.py", maps_path, ROOT / "test_sparse_outer_match.py",
        ROOT / "peel_sparse_outer_collar.cpp", ROOT / "peel_sparse_outer_collar-linux",
        ROOT / "sparse_outer_matcher.inc", ROOT / "peel_outer_collar.cpp", ROOT / "derive_sparse_collar.py",
        ROOT / "sparse-collar-source-derivation.json", basepath, ROOT / "test_outer_collar.py",
        HIGH / "peel_degree.cpp", HIGH / "paid_outer_matcher.inc",
        ROOT / "OUTER-COLLAR-REDUCTION-DRAFT.md", ROOT / "SPARSE-OUTER-OBSTACLE-TRANSPORT.md",
    ):
        bind(files, p)
    for extra in ("family_sparse_gate.py", "derive_generic_sparse_driver.py",
                  "generic-sparse-driver-derivation.json"):
        bind(files, ROOT / extra)
    output.mkdir(parents=True)
    target = output / "N25-B14-necessary-sparse-collars.json"
    relative = os.path.relpath(target, ROOT).replace("\\", "/")
    table_relative = os.path.relpath(table, ROOT).replace("\\", "/")
    assert relative.isascii() and table_relative.isascii()
    command = [WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
               "./peel_sparse_outer_collar-linux", "25", str(B), relative,
               str(constants["angle_scale"]), *map(str, constants["angle_caps"]), "0", "dfs", "-", table_relative]
    publish(output / "INPUT-BINDINGS.json", {
        "N": 25, "B": B, "command": command, "files_relative_to_workspace": files,
        "native_platform": "new WSL Ubuntu2204 static executable",
        "old_sources_and_results_preserved": True, "global_optimality_proved": False,
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
        publish(output / "WSL-LAUNCH.json", {"owned_wsl_proxy_pid": process.pid, "command": command,
                                          "input_bindings_sha256": sha(output / "INPUT-BINDINGS.json")})
        print("N25/B15 sparse necessary search dispatched; WSL proxy", process.pid, flush=True)
        while True:
            try:
                code = process.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                if native_pid is None:
                    text = (output / "NATIVE-STDERR.log").read_text(encoding="utf8", errors="replace")
                    match = re.search(r"COLLAR NATIVE PID=(\d+) N=25 B=B", text)
                    if match:
                        native_pid = int(match.group(1))
                        publish(output / "LINUX-NATIVE-IDENTITY.json", {
                            "linux_native_pid": native_pid, "binary_linux_path": linux_path(ROOT / "peel_sparse_outer_collar-linux"),
                            "native_binary_sha256": sha(ROOT / "peel_sparse_outer_collar-linux"),
                            "owned_wsl_proxy_pid": process.pid,
                            "check_proc_identity_before_any_signal": True,
                        })
                        print("Actual sparse Linux native PID", native_pid, flush=True)
        collector.join(timeout=30)
        assert not collector.is_alive()
        process.stdout.close()
    text = (output / "NATIVE-STDERR.log").read_text(encoding="utf8", errors="replace")
    match = re.search(r"COLLAR NATIVE PID=(\d+) N=25 B=B", text)
    if match:
        native_pid = int(match.group(1))
    publish(output / "NATIVE-TERMINAL.json", {
        "native_terminal_observed": True, "actual_exit_code": code, "linux_native_pid": native_pid,
        "owned_wsl_proxy_pid": process.pid, "seconds": time.monotonic()-started,
        "native_log_sha256": sha(output / "NATIVE-STDERR.log"), "global_optimality_proved": False,
    })
    assert code == 0, "nonzero, memory- or node-limited search is incomplete"
    unchanged(files)
    header, codes = collar_codes(target, 25, B)
    assert header["mode"] == "dfs" and header["screen"]
    assert header["scale"] == constants["angle_scale"] and header["caps"] == constants["angle_caps"]
    assert header["sparse_patterns_loaded"] == library["obstacle_count"]
    assert header["paid_patterns_loaded"] == 0
    byid = {o["id"]: o for o in library["obstacles"]}
    for payment in header["sparse_payments"]:
        mapping = {k: payment[k] for k in ("centers", "anchors", "orientation", "shift")}
        validate(25, B, byid[payment["obstacle"]]["faces"], mapping, payment["sample_faces"])
    groups = [{"id": i, **row, "members": 1} for i, row in enumerate(header["weak_graphs"])]
    bindingpath = output / "bindings.jsonl"
    with bindingpath.open("x", encoding="utf8") as stream:
        for i, group in enumerate(groups):
            stream.write(json.dumps({
                "index": i, "group": i, "map": {
                    "centers": list(range(group["centers"])), "anchors": list(range(B)), "orientation": 1, "shift": 0},
            }, separators=(",", ":"))+"\n")
    publish(output / "GROUPS.json", {
        "N": 25, "B": B, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups), "catalog_sha256": sha(target),
        "bindings_file": bindingpath.name, "bindings_sha256": sha(bindingpath),
        "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": True,
        "parent_groups_sha256": None, "parent_proof_sha256": None, "source_sha256": sha(Path(__file__)),
        "members_are_necessary_weak_graphs_not_full_types": True, "global_optimality_proved": False,
    })
    unchanged(files)
    publish(output / "SUMMARY.json", {
        "verified": True, "N": 25, "B": B, "complete_necessary_outer_collar_overapproximation": True,
        "unpaid_weak_graphs": len(groups), "all_remaining_weak_lower_bounds_paid": len(groups) == 0,
        "full_triangulations_not_enumerated": True, "source_induction_required_for_cover_transport": True,
        "native_catalog_sha256": sha(target), "groups_sha256": sha(output / "GROUPS.json"),
        "payment_samples_explicitly_mapped": len(header["sparse_payments"]),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("N25/B15 sparse necessary search and catalogue verified:", len(groups), "remaining weak graphs", flush=True)


if __name__ == "__main__":
    main()
