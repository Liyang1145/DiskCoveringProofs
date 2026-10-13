"""Complete small-family partitions for the isolated cached origin enumerator."""
from pathlib import Path
import argparse
import json
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
from n25_outer_search import read, publish, bind, unchanged
from cached_support_gate import derivation_gate
from family_sparse_gate import sparse_library_gate
from test_origin_collar import relative
from test_outer_collar import linux_path, WSL, collar_codes
from test_streamed_collar import codes_from_union
from merge_origin_collar_chunks import merge

assert __debug__


def native_logged(binary, arguments, directory):
    command = [WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env",
               "-C", linux_path(ROOT), "./"+binary, *map(str, arguments)]
    started = time.monotonic()
    log_path = directory / "NATIVE-STDERR.log"
    with log_path.open("xb") as log:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        publish(directory / "WSL-LAUNCH.json", {"command": command, "owned_wsl_proxy_pid": process.pid})
        def collect():
            for line in iter(process.stdout.readline, b""):
                log.write(line);log.flush()
        collector = threading.Thread(target=collect, daemon=True)
        collector.start()
        code = process.wait()
        collector.join(timeout=30)
        assert not collector.is_alive()
        process.stdout.close()
    log_text = log_path.read_text(encoding="utf8", errors="replace")
    identity = re.search(r"COVER ORIGIN NATIVE PID=(\d+) N=(\d+) B=(\d+)", log_text)
    seconds = time.monotonic()-started
    publish(directory / "NATIVE-TERMINAL.json", {
        "native_terminal_observed": True, "actual_exit_code": code,
        "linux_native_pid": int(identity.group(1)) if identity else None,
        "seconds": seconds, "native_log_sha256": sha(log_path),
        "command": command, "only_a_control_not_a_full_N25_boundary_family": True,
    })
    return code, seconds


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    files = derivation_gate()
    library_path = ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"
    constants, library, table, dependencies = sparse_library_gate(library_path)
    files.update(dependencies)
    assert library["B"] == 16 and library["obstacle_count"] == 164
    map_control_path = ROOT / "n25-B16-cached-support-map-controls-20261005-v1/VERIFIED.json"
    maps = read(map_control_path)
    assert maps["verified"] and maps["schema"] == "bounded-sparse-support-cache-map-controls-v1"
    assert maps["source_sha256"] == sha(ROOT / "test_cached_sparse_support.py")
    assert maps["library_sha256"] == sha(library_path)
    assert maps["all_old_new_first_positive_maps_identical"]
    assert maps["known_attaining_result_unchanged_from_frozen_control"]
    assert maps["native_binary_sha256"] == sha(ROOT / "sparse_support_cached_match-linux")
    unchanged(maps["files_relative_to_workspace"])
    files.update(maps["files_relative_to_workspace"])
    reference_root = ROOT / "n25-B16-eight-sparse-guard-controls-20261005-v1"
    reference_control = read(reference_root / "VERIFIED.json")
    assert reference_control["verified"] and reference_control["all_baseline_minus_residual_graphs_individually_paid"]
    unchanged(reference_control["files_relative_to_workspace"])
    output.mkdir()
    by_id = {row["id"]: row for row in library["obstacles"]}
    cases = []
    for N in (22, 23):
        reference = reference_root / f"N{N}-B16-eight-baseline.json"
        declared = next(row for row in reference_control["cases"] if row["N"] == N and row["mode"] == "dfs")
        assert sha(reference) == declared["baseline_sha256"]
        baseline, expected = collar_codes(reference, N, 16)
        target_centers = {tuple(row["faces"]): row["centers"] for row in baseline["weak_graphs"]}
        for mode in ("dfs", "audit"):
            directory = output / f"N{N}-{mode}"
            directory.mkdir()
            manifest_path = directory / "MANIFEST.json"
            print("Cached origin complete control dispatched:", N, 16, mode, flush=True)
            code, seconds = native_logged("peel_cached_support_origin_collar-linux", [
                N, 16, relative(manifest_path), constants["angle_scale"], *constants["angle_caps"],
                0, mode, "-", relative(table), "4058615", 100000, 1,
            ], directory)
            assert code == 0
            manifest = read(manifest_path)
            assert manifest["origin_cover_prunes_not_type_count"] == 0
            assert manifest["N"] == N and manifest["B"] == 16
            assert manifest["screen"] and manifest["eight_rod_screen"] and manifest["origin_cover_screen"]
            assert manifest["mode"] == mode and manifest["complete_necessary_outer_search"]
            union = merge(manifest_path, 0, directory / "UNION")
            header, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
            assert actual <= expected
            removed = sorted(expected-actual)
            requests_path = directory / "REMOVED-REQUESTS.tsv"
            with requests_path.open("x", encoding="ascii") as stream:
                for index, faces in enumerate(removed):
                    stream.write("\t".join(map(str, [index, len(faces), *faces]))+"\n")
            answers_path = directory / "REMOVED-MAPS.json"
            (directory / "removed-native").mkdir()
            answer_code, _ = native_logged("sparse_support_cached_match-linux", [
                "match", N, 16, relative(table), relative(requests_path), relative(answers_path),
            ], directory / "removed-native")
            assert answer_code == 0
            answers = read(answers_path)
            assert answers["scope"] == "sparse subgraph maps only"
            assert len(answers["matches"]) == len(removed)
            accepted_maps = directory / "REMOVED-MAPS-CHECKED.jsonl"
            with accepted_maps.open("x", encoding="ascii") as stream:
                for index, (faces, answer) in enumerate(zip(removed, answers["matches"], strict=True)):
                    assert answer["request"] == index and answer["obstacle"] in by_id
                    obstacle = by_id[answer["obstacle"]]
                    mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
                    assert len(mapping["centers"]) == obstacle["centers"]
                    validate(target_centers[faces], 16, obstacle["faces"], mapping, faces)
                    stream.write(json.dumps({"faces": list(faces), "obstacle": obstacle["id"], "map": mapping},
                                            separators=(",", ":"))+"\n")
            for payment in manifest["sparse_payments"]:
                obstacle = by_id[payment["obstacle"]]
                mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
                validate(N, 16, obstacle["faces"], mapping, payment["sample_faces"])
            cases.append({
                "N": N, "B": 16, "mode": mode, "baseline_weak_graphs": len(expected),
                "residual_weak_graphs": len(actual), "all_removed_graphs_explicitly_strictly_paid": True,
                "removed_graphs": len(removed), "baseline_calls": baseline["calls"],
                "new_calls": manifest["calls"], "new_seconds": seconds,
                "manifest_sha256": sha(manifest_path), "union_sha256": sha(directory / "UNION/VERIFIED.json"),
                "accepted_removed_maps_sha256": sha(accepted_maps),
            })
            for path in (manifest_path, directory / "NATIVE-TERMINAL.json",
                         directory / "UNION/VERIFIED.json", directory / "UNION/CATALOG.jsonl",
                         requests_path, answers_path, accepted_maps, reference):
                bind(files, path)
            print("Cached origin complete partition PASS:", N, mode, len(expected),
                  "->", len(actual), "weak graphs;", round(seconds, 2), "seconds", flush=True)
    negatives = []
    for label, N, B, limit, flag in (
        ("node-limit", 25, 16, 1, 1), ("bad-flag", 25, 16, 0, 2), ("bad-N", 26, 16, 0, 1),
    ):
        directory = output / label
        directory.mkdir()
        target = directory / "MANIFEST.json"
        code, _ = native_logged("peel_cached_support_origin_collar-linux", [
            N, B, relative(target), constants["angle_scale"], *constants["angle_caps"],
            limit, "dfs", "-", relative(table), "4058615", 100000, flag,
        ], directory)
        assert code != 0 and not target.exists()
        negatives.append(label)
    for path in (Path(__file__), map_control_path, library_path, reference_root / "VERIFIED.json",
                 ROOT / "peel_cached_support_origin_collar-linux", ROOT / "sparse_support_cached_match-linux",
                 ROOT / "cached_support_gate.py", ROOT / "SPARSE-SUPPORT-CACHE-SOURCE.md",
                 ROOT / "test_origin_collar.py", ROOT / "merge_origin_collar_chunks.py"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "cached-support-origin-complete-partition-controls-v1",
        "N": 25, "B": 16, "cases": cases,
        "all_four_complete_small_family_partitions_paid": True,
        "all_native_sparse_positive_samples_checked": True,
        "origin_condition_inactive_below_N25_confirmed": True,
        "negative_controls_rejected": negatives, "library_sha256": sha(library_path),
        "map_controls_sha256": sha(map_control_path), "source_sha256": sha(Path(__file__)),
        "native_binary_sha256": sha(ROOT / "peel_cached_support_origin_collar-linux"),
        "files_relative_to_workspace": files, "not_a_complete_N25_boundary_family": True,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
