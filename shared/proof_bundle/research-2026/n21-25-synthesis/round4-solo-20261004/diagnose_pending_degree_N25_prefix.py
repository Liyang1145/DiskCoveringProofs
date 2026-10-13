"""Bounded, explicitly incomplete N25 timing diagnostic; not a proof receipt."""
from pathlib import Path
import argparse
import statistics
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
from test_pending_degree_upper_small import derivation_gate
from test_cached_support_origin_partition import native_logged
from test_origin_collar import relative

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--node-limit", type=int, default=250000)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    assert 1 <= args.node_limit <= 1000000
    derivation, original, target = derivation_gate()
    control_path = ROOT / "n25-pending-degree-upper-full-controls-20261005-v1/VERIFIED.json"
    controls = read(control_path)
    assert controls["verified"] and controls["known_N25_attaining_seed_explicitly_retained"]
    assert controls["source_sha256"] == sha(ROOT / "test_pending_degree_upper_controls.py")
    unchanged(controls["files_relative_to_workspace"])
    files = dict(controls["files_relative_to_workspace"])
    libraries = {}
    for count, name in (
        (9, "n25-B15-new-sparse-library-20261005-v1"),
        (27, "n25-B15-offline-contracted-union27-library-20261005-v1"),
    ):
        path = ROOT / name / "LIBRARY.json"
        constants, library, table, dependencies = sparse_library_gate(path)
        assert library["B"] == 15 and library["obstacle_count"] == count
        files.update(dependencies)
        libraries[count] = (path, table)
    output.mkdir()
    cases = []
    configurations = [
        ("original-nine", "peel_origin_streamed_collar-linux", 9, None),
        ("cached-nine", "peel_cached_support_origin_collar-linux", 9, None),
        ("pending-upper-nine", "peel_pending_degree_origin_collar-linux", 9, 1),
        ("pending-upper-twentyseven", "peel_pending_degree_origin_collar-linux", 27, 1),
    ]
    for repetition in range(3):
        for name, binary, count, flag in configurations:
            directory = output / f"repeat{repetition}-{name}"
            directory.mkdir()
            path, table = libraries[count]
            manifest_path = directory / "INCOMPLETE-MANIFEST.json"
            arguments = [
                25, 15, relative(manifest_path), constants["angle_scale"], *constants["angle_caps"],
                args.node_limit, "dfs", "-", relative(table), 4058615, 100000, 1,
            ]
            if flag is not None:
                arguments.append(flag)
            code, seconds = native_logged(binary, arguments, directory)
            assert code != 0 and not manifest_path.exists()
            log_path = directory / "NATIVE-STDERR.log"
            assert "REJECTED NODE LIMIT: incomplete collar search, no completion" in log_path.read_text(encoding="utf8")
            terminal = read(directory / "NATIVE-TERMINAL.json")
            assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == code
            cases.append({
                "configuration": name, "repetition": repetition, "N": 25, "B": 15,
                "requested_node_limit": args.node_limit, "actual_exit_code": code, "seconds": seconds,
                "native_binary_sha256": sha(ROOT / binary), "library_sha256": sha(path),
                "manifest_absent_and_expected_node_limit_rejection": True,
                "incomplete_not_a_full_family_or_a_geometric_payment": True,
            })
            for item in (log_path, directory / "NATIVE-TERMINAL.json", directory / "WSL-LAUNCH.json",
                         ROOT / binary, path):
                bind(files, item)
            print("Incomplete N25 prefix timing:", name, repetition, round(seconds, 3),
                  "seconds; expected nonzero NODE LIMIT", flush=True)
    medians = {
        name: statistics.median(row["seconds"] for row in cases if row["configuration"] == name)
        for name, *_ in configurations
    }
    for path in (Path(__file__), control_path, derivation, original, target):
        bind(files, path)
    unchanged(files)
    publish(output / "DIAGNOSTIC.json", {
        "schema": "explicitly-incomplete-N25-pending-degree-prefix-timing-v1",
        "cases": cases, "median_seconds_by_configuration": medians,
        "all_runs_intentionally_incomplete_and_actual_nonzero_exit_observed": True,
        "not_full_production_controls_or_restart_approval": True,
        "different_pruning_makes_equal_call_prefixes_different_search_work": True,
        "no_complete_boundary_family_or_geometric_payment_claimed": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
