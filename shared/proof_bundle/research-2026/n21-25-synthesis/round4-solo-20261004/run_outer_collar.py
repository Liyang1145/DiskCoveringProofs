"""Content-gated new-platform necessary collar search for one n25 family."""
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
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from audit_streamed_hierarchy import check_map
from n25_outer_search import library_gate, kernel_gate, read, bind, unchanged, publish
from test_outer_collar import linux_path, collar_codes, source_derivation, WSL

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--B", type=int, choices=(14,), required=True)
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT.resolve()) and output != ROOT.resolve() and not output.exists()
    constants, library, table, files = library_gate(args.library.resolve())
    kernel_gate(files)
    controls = read(args.controls)
    assert controls["verified"] and controls["native_source_sha256"] == sha(ROOT / "peel_outer_collar.cpp")
    assert controls["native_binary_sha256"] == sha(ROOT / "peel_outer_collar-linux")
    assert controls["source_sha256"] == sha(ROOT / "test_outer_collar.py")
    assert controls["frozen_degree_source_sha256"] == sha(HIGH / "peel_degree.cpp")
    assert controls["frozen_outer_matcher_sha256"] == sha(HIGH / "paid_outer_matcher.inc")
    assert controls["all_full_reference_outer_restrictions_present"]
    assert controls["splitting_recursion_mechanically_preserved_except_recursive_name_and_omission_accounting"]
    assert len(controls["cases"]) == 18 and any(row["N"]-row["B"] == 8 for row in controls["cases"])
    assert controls["same_B14_actual_library_pruning_reference_containment"]
    assert set(controls["negative_controls_rejected"]) == {"node-limit", "bad-N", "bad-B"}
    source_derivation()
    for path in (
        Path(__file__), args.controls, ROOT / "test_outer_collar.py",
        ROOT / "peel_outer_collar.cpp", ROOT / "peel_outer_collar-linux",
        HIGH / "peel_degree.cpp", HIGH / "paid_outer_matcher.inc",
        ROOT / "OUTER-COLLAR-REDUCTION-DRAFT.md",
    ):
        bind(files, path)
    output.mkdir(parents=True)
    target = output / "N25-B14-necessary-collars.json"
    target_relative = os.path.relpath(target, ROOT).replace("\\", "/")
    table_relative = os.path.relpath(table, ROOT).replace("\\", "/")
    assert target_relative.isascii() and table_relative.isascii()
    command = [
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./peel_outer_collar-linux", "25", "14", target_relative,
        str(constants["angle_scale"]), *map(str, constants["angle_caps"]), "0", "dfs", table_relative,
    ]
    publish(output / "INPUT-BINDINGS.json", {
        "N": 25, "B": 14, "command": command, "files_relative_to_workspace": files,
        "native_platform": "new WSL Ubuntu2204 statically linked executable",
        "overapproximation_not_full_triangulation_catalogue": True,
        "source_induction_and_small_controls_are_separate_from_native_completion": True,
        "global_optimality_proved": False,
    })
    started = time.monotonic()
    native_pid = None
    with (output / "NATIVE-STDERR.log").open("xb") as log:
        # This server's legacy WSL requires pipe handles. A direct redirected
        # disk handle terminates the WSL proxy before native startup.
        process = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        def collect():
            for chunk in iter(process.stdout.readline, b""):
                log.write(chunk)
                log.flush()
        collector = threading.Thread(target=collect, daemon=True)
        collector.start()
        publish(output / "WSL-LAUNCH.json", {
            "owned_windows_wsl_proxy_pid": process.pid, "command": command,
            "input_bindings_sha256": sha(output / "INPUT-BINDINGS.json"),
        })
        print("N25/B14 necessary outer-collar search dispatched; WSL proxy", process.pid, flush=True)
        while True:
            try:
                code = process.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                if native_pid is None:
                    text = (output / "NATIVE-STDERR.log").read_text(encoding="utf8", errors="replace")
                    match = re.search(r"COLLAR NATIVE PID=(\d+) N=25 B=14", text)
                    if match:
                        native_pid = int(match.group(1))
                        publish(output / "LINUX-NATIVE-IDENTITY.json", {
                            "linux_native_pid": native_pid, "binary_linux_path": linux_path(ROOT / "peel_outer_collar-linux"),
                            "binary_sha256": sha(ROOT / "peel_outer_collar-linux"),
                            "working_directory_linux_path": linux_path(ROOT),
                            "owned_wsl_proxy_pid": process.pid,
                            "do_not_signal_pid_without_rechecking_proc_cmdline_and_start_identity": True,
                        })
                        print("Actual Linux collar native PID", native_pid, flush=True)
        collector.join(timeout=30)
        assert not collector.is_alive(), "native output collection did not reach EOF"
        process.stdout.close()
    text = (output / "NATIVE-STDERR.log").read_text(encoding="utf8", errors="replace")
    match = re.search(r"COLLAR NATIVE PID=(\d+) N=25 B=14", text)
    if match:
        native_pid = int(match.group(1))
    publish(output / "NATIVE-TERMINAL.json", {
        "native_terminal_observed": True, "actual_exit_code": code, "linux_native_pid": native_pid,
        "owned_wsl_proxy_pid": process.pid, "native_log_sha256": sha(output / "NATIVE-STDERR.log"),
        "seconds": time.monotonic()-started, "global_optimality_proved": False,
    })
    assert code == 0, "failed/budgeted collar search is never complete"
    unchanged(files)
    header, codes = collar_codes(target, 25, 14)
    assert header["mode"] == "dfs" and header["screen"]
    assert header["scale"] == constants["angle_scale"] and header["caps"] == constants["angle_caps"]
    assert header["paid_patterns_loaded"] == library["obstacle_count"]
    for payment in header["proof_payments"]:
        obstacle = library["obstacles"][payment["obstacle"]]
        mapping = {k: payment[k] for k in ("centers", "anchors", "orientation", "shift")}
        check_map(25, 14, obstacle, mapping, set(payment["sample_faces"]), 1)
    # The direct weak catalogue is a sufficient necessary overapproximation.
    # These members are weak graph rows, NOT original full-type counts.
    groups = [{"id": i, **row, "members": 1} for i, row in enumerate(header["weak_graphs"])]
    bindingpath = output / "bindings.jsonl"
    with bindingpath.open("x", encoding="utf8") as stream:
        for i, group in enumerate(groups):
            stream.write(json.dumps({
                "index": i, "group": i,
                "map": {"centers": list(range(group["centers"])), "anchors": list(range(14)),
                        "orientation": 1, "shift": 0},
            }, separators=(",", ":")) + "\n")
    publish(output / "GROUPS.json", {
        "N": 25, "B": 14, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups), "catalog_sha256": sha(target),
        "bindings_file": bindingpath.name, "bindings_sha256": sha(bindingpath),
        "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": True, "parent_groups_sha256": None, "parent_proof_sha256": None,
        "source_sha256": sha(Path(__file__)), "members_are_necessary_weak_graph_rows_not_full_types": True,
        "global_optimality_proved": False,
    })
    unchanged(files)
    publish(output / "SUMMARY.json", {
        "verified": True, "N": 25, "B": 14, "complete_necessary_outer_collar_overapproximation": True,
        "full_triangulation_catalogue_not_enumerated": True, "unpaid_weak_graphs": len(groups),
        "all_remaining_weak_lower_bounds_paid": len(groups) == 0,
        "source_induction_required_for_full_cover_transport": True,
        "payment_samples_explicitly_mapped": len(header["proof_payments"]),
        "native_catalog_sha256": sha(target), "groups_sha256": sha(output / "GROUPS.json"),
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("N25/B14 necessary outer-collar catalogue verified:", len(groups),
          "unpaid weak graphs; still not the all-n25 theorem", flush=True)


if __name__ == "__main__":
    main()
