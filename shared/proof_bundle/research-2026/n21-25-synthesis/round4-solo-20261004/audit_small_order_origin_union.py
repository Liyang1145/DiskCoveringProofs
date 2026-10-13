"""Recheck actual small-order source/terminal gates, then independent full union."""
from pathlib import Path
import argparse
import os
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from small_order_origin_caps import parameters
from merge_small_order_origin_chunks import merge, gate
from test_outer_collar import WSL, linux_path

assert __debug__


def inputs_gate(stage, controls_path, caps_path):
    inputs, terminal, launch, controls, caps_report = map(read, (
        stage / "INPUT-BINDINGS.json", stage / "NATIVE-TERMINAL.json",
        stage / "NATIVE-LAUNCH.json", controls_path, caps_path))
    N, B = inputs["N"], inputs["B"]
    assert N in (23, 24) and type(N) is int and type(B) is int
    constants, cap8, cap_record = parameters(N)
    assert [B, N-B] in constants["families"]
    assert controls["verified"] and controls["schema"] == "small-order-origin-collar-complete-source-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_small_order_origin_collar.py")
    assert controls["all_original_recursive_and_canonical_branches_literally_unchanged"]
    assert controls["both_N23_N24_true_attaining_graphs_retained_by_origin_and_own_angles"]
    assert len(controls["complete_reference_containment_cases"]) == 10
    assert len(controls["actual_attaining_and_functional_native_origin_angle_checks"]) == 64
    assert len(controls["negative_controls_rejected"]) == 12
    assert caps_report["verified"] and caps_report["source_sha256"] == sha(ROOT / "small_order_origin_caps.py")
    assert cap_record == next(row for row in caps_report["orders"] if row["N"] == N)
    assert inputs["controls_sha256"] == sha(controls_path) and inputs["caps_report_sha256"] == sha(caps_path)
    assert inputs["source_sha256"] == sha(ROOT / "run_small_order_origin_search.py")
    assert inputs["source_not_restricted_to_a_seed_or_discovery_sample"]
    manifestpath = stage / "MANIFEST.json"
    relative = os.path.relpath(manifestpath, ROOT).replace("\\", "/")
    assert relative.isascii()
    expected = list(map(str, [
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./peel_small_order_origin_collar-linux", N, B, relative, constants["angle_scale"],
        *constants["angle_caps"], 0, "dfs", "-", "-", cap8, 100000, 1]))
    assert inputs["command"] == launch["command"] == terminal["command"] == expected
    assert launch["input_bindings_sha256"] == terminal["input_bindings_sha256"] == sha(stage / "INPUT-BINDINGS.json")
    assert launch["windows_native_launcher_pid"] == terminal["windows_native_launcher_pid"]
    assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["source_sha256"] == sha(ROOT / "run_small_order_origin_search.py")
    assert terminal["native_log_sha256"] == sha(stage / "NATIVE-STDOUT-STDERR.log")
    assert terminal["manifest_sha256"] == sha(manifestpath)
    manifest = read(manifestpath)
    assert gate(manifest) == (N, B)
    assert manifest["origin_cover_screen"] and manifest["screen"] and manifest["eight_rod_screen"]
    assert manifest["mode"] == "dfs" and manifest["scale"] == constants["angle_scale"]
    assert manifest["caps"] == constants["angle_caps"] and manifest["cap8"] == cap8
    assert manifest["slab_limit"] == 100000
    assert not manifest.get("seeded_fixed_collar_restriction", False)
    assert inputs["original_sources_and_existing_proof_jobs_not_edited"]
    files = dict(inputs["frozen_files"])
    for path, digest in controls["frozen_files"].items():
        assert path in files and files[path] == digest
    for path, digest in files.items():
        assert sha(path) == digest
    return manifestpath, inputs, files


def main():
    ap = argparse.ArgumentParser()
    for name in ("stage", "controls", "caps", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    stage, controlpath, cappath, output = (
        getattr(args, name).resolve() for name in ("stage", "controls", "caps", "output"))
    assert all(path.is_relative_to(ROOT) for path in (stage, controlpath, cappath, output))
    assert not output.exists()
    manifestpath, inputs, frozen = inputs_gate(stage, controlpath, cappath)
    union = merge(manifestpath, 0, output)
    for path in (Path(__file__), manifestpath, stage / "INPUT-BINDINGS.json",
                 stage / "NATIVE-LAUNCH.json", stage / "NATIVE-TERMINAL.json",
                 stage / "NATIVE-STDOUT-STDERR.log", controlpath, cappath,
                 output / "VERIFIED.json", output / "CATALOG.jsonl", output / "bindings.jsonl"):
        frozen[str(path)] = sha(path)
    for chunk in union["input_chunks"]:
        path = stage / chunk["file"]
        assert sha(path) == chunk["sha256"]
        frozen[str(path)] = chunk["sha256"]
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "SOURCE-ACCEPTED.json", {
        "verified": True, "schema": "small-order-complete-necessary-origin-outer-family-source-and-union-v1",
        "N": inputs["N"], "B": inputs["B"],
        "complete_recorded_necessary_outer_family": True,
        "actual_native_successful_terminal_and_exact_source_inputs_rechecked": True,
        "all_declared_sorted_slabs_and_full_union_independently_verified": True,
        "unique_necessary_weak_graphs": union["unique_necessary_weak_graphs"],
        "catalog_sha256": union["catalog_sha256"], "union_report_sha256": sha(output / "VERIFIED.json"),
        "weak_graph_rows_not_full_type_lower_bound_payments": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "every_residual_lower_bound_and_actual_cover_global_synthesis_still_required": True,
        "global_optimality_proved": False,
    })
    print("Small-order actual complete source and entire union accepted:", inputs["N"], inputs["B"],
          union["unique_necessary_weak_graphs"], "necessary weak graphs; not global proof", flush=True)


if __name__ == "__main__":
    main()
