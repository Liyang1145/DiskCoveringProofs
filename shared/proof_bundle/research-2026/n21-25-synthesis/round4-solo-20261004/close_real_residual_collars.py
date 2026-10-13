"""Sequential, bounded completion payments for an independently replayed prefix."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog", type=Path, required=True)
    ap.add_argument("--prefix", type=Path, required=True)
    ap.add_argument("--skip-closure", type=Path, action="append", default=[])
    ap.add_argument("--residual", type=Path, required=True)
    ap.add_argument("--exclude-selection", type=Path, action="append", default=[])
    ap.add_argument("--count", type=int, default=5)
    ap.add_argument("--node-limit", type=int, default=1000000)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    catalog, prefix, output = (p.resolve() for p in (args.catalog, args.prefix, args.output))
    assert output.is_relative_to(ROOT) and not output.exists()
    assert 1 <= args.count <= 100 and 1 <= args.node_limit <= 10000000
    source, replay = read(catalog / "SUMMARY.json"), read(prefix / "VERIFIED.json")
    assert replay["verified"] and replay["schema"] == "completed-collar-force-prefix-exact-replay-v1"
    assert replay["all_selected_strict_trees_fresh_exact_replayed"] and replay["all_selected_parent_identity_maps_checked"]
    assert replay["source_sha256"] == sha(ROOT / "replay_completed_collar_prefix.py")
    assert replay["source_catalog_summary_sha256"] == sha(catalog / "SUMMARY.json")
    assert replay["groups_sha256"] == source["groups_sha256"] == sha(catalog / "GROUPS.json")
    assert sha(prefix / "PENDING.jsonl") == replay["pending_sha256"]
    assert source["complete_necessary_outer_collar_overapproximation"] and source["N"] == 25
    unchanged(source["files_relative_to_workspace"])
    paid = {}
    for path in args.skip_closure:
        closure = read(path)
        assert closure["verified"] and closure["pending_completions"] == 0
        assert closure["schema"] == "single-collar-strict-full-completion-closure-v1"
        assert closure["source_sha256"] == sha(ROOT / "close_strict_collar_family.py")
        unchanged(closure["files_relative_to_workspace"])
        assert (closure["N"], closure["B"]) == (source["N"], source["B"])
        paid[tuple(closure["collar_faces"])] = path.resolve()
    residual_root = args.residual.resolve()
    partition = read(residual_root / "VERIFIED.json")
    assert partition["verified"] and partition["all_complete_parent_rows_processed_once"]
    assert partition["schema"] == "complete-old-collar-independent-paid-partition-v1"
    assert partition["source_sha256"] == sha(ROOT / "filter_complete_collar_cached.py")
    unchanged(partition["files_relative_to_workspace"])
    assert (partition["N"], partition["B"]) == (source["N"], source["B"])
    assert partition["parent_groups_sha256"] == source["groups_sha256"]
    assert sha(residual_root / "RESIDUAL.jsonl") == partition["residual_sha256"]
    residual_ids, last = set(), -1
    with (residual_root / "RESIDUAL.jsonl").open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header["source_catalog_sha256"] == source["groups_sha256"]
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert last < row["id"] < partition["parent_weak_graphs"]
            last = row["id"]
            residual_ids.add(last)
    assert len(residual_ids) == partition["residual_weak_graphs"]
    excluded_running = set()
    excluded_selection_hashes = []
    for path in args.exclude_selection:
        selection = read(path)
        assert selection["parent_complete_catalog_sha256"] == source["groups_sha256"]
        excluded_running.update(selection["selected_parent_groups"])
        excluded_selection_hashes.append(sha(path))
    selected = []
    with (prefix / "PENDING.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert row["not_an_exclusion"]
            if row["group"] not in residual_ids or row["group"] in excluded_running:
                continue
            if tuple(row["faces"]) in paid:
                continue
            selected.append(row)
            if len(selected) == args.count:
                break
    assert selected
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "parent_complete_catalog_sha256": source["groups_sha256"],
        "parent_summary_sha256": sha(catalog / "SUMMARY.json"),
        "exact_prefix_sha256": sha(prefix / "VERIFIED.json"),
        "pending_prefix_sha256": sha(prefix / "PENDING.jsonl"),
        "selected_parent_groups": [r["group"] for r in selected],
        "real_residual_report_sha256": sha(residual_root / "VERIFIED.json"),
        "real_residual_sha256": partition["residual_sha256"],
        "excluded_running_selection_sha256": excluded_selection_hashes,
        "selected_only_actual_unpaid_parents": True,
        "node_limit_per_completion_family": args.node_limit,
        "source_sha256": sha(Path(__file__)), "not_an_entire_boundary_family": True,
        "global_optimality_proved": False,
    })
    environment = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1")

    def invoke(path, arguments, directory, label):
        result = subprocess.run([sys.executable, str(path), *map(str, arguments)],
                                capture_output=True, env=environment,
                                creationflags=subprocess.CREATE_NO_WINDOW)
        publish(directory / (label+"-TERMINAL.json"), {
            "actual_exit_code": result.returncode, "process_terminal_observed": True,
            "source_sha256": sha(path), "stdout": result.stdout.decode("utf8", errors="replace"),
            "stderr": result.stderr.decode("utf8", errors="replace"),
        })
        return result.returncode

    results = []
    for row in selected:
        gid = row["group"]
        directory = output / f"parent-{gid:07}"
        directory.mkdir()
        family = directory / "COMPLETIONS"
        status = {"parent_group": gid, "status": "unpaid", "not_a_geometric_weak_exclusion": True}
        code = invoke(ROOT / "complete_simple_collar.py",
                      ["--groups", catalog / "GROUPS.json", "--group", gid,
                       "--limit", args.node_limit, "--output", family], directory, "ENUMERATE")
        if code != 0:
            status["reason"] = "completion enumeration failed or hit its node limit; not complete"
        elif (family / "UNHANDLED.json").exists():
            status["reason"] = "pinched/nonmanifold collar unhandled; no exclusion"
        else:
            input_collar = read(family / "INPUT-COLLAR.json")
            assert (input_collar["centers"], input_collar["faces"]) == (row["centers"], row["faces"])
            groups = read(family / "GROUPS.json")
            status["full_completion_types"] = groups["group_count"]
            proposal = directory / "PROPOSALS"
            code = invoke(HIGH / "probe_groups.py", ["--groups", family / "GROUPS.json",
                                                    "--output", proposal, "--limit", 1], directory, "PROPOSE")
            if code == 0:
                receipt = read(proposal / "SUMMARY.json")
                exact = directory / "EXACT-REPLAY.json"
                code = invoke(HIGH / "replay_group_stage.py",
                              ["--groups", family / "GROUPS.json", "--receipt", proposal / "SUMMARY.json",
                               "--output", exact], directory, "REPLAY")
                if code == 0 and receipt["pending_groups"] == 0:
                    closurepath = directory / "CLOSURE.json"
                    code = invoke(ROOT / "close_strict_collar_family.py",
                                  ["--catalog-root", family, "--receipt", proposal / "SUMMARY.json",
                                   "--replay", exact, "--output", closurepath], directory, "CLOSE")
                    if code == 0:
                        closure = read(closurepath)
                        assert closure["pending_completions"] == 0
                        assert (closure["collar_centers"], closure["collar_faces"]) == (row["centers"], row["faces"])
                        status.update(status="full-simple-disk-completion-family-strictly-paid",
                                      closure_file=closurepath.relative_to(output).as_posix(),
                                      closure_sha256=sha(closurepath), pending_completions=0)
                elif code == 0:
                    status["reason"] = "some full completions still pending exact lower bounds"
                    status["pending_completions"] = receipt["pending_groups"]
            if code != 0:
                status["reason"] = "a proof/replay/closure process failed; family remains unpaid"
        results.append(status)
        publish(directory / "STATUS.json", status)
        print("Fixed outer collar", gid, status["status"],
              status.get("full_completion_types"), "full types;", status.get("reason", ""), flush=True)
    assert sha(residual_root / "RESIDUAL.jsonl") == partition["residual_sha256"]
    assert [sha(path) for path in args.exclude_selection] == excluded_selection_hashes
    assert sha(catalog / "GROUPS.json") == source["groups_sha256"]
    assert sha(prefix / "PENDING.jsonl") == replay["pending_sha256"]
    unchanged(source["files_relative_to_workspace"])
    publish(output / "SUMMARY.json", {
        "verified": True, "N": source["N"], "B": source["B"],
        "selected_prefix_pending_families": len(results),
        "strictly_paid_completion_families": sum(r["status"] == "full-simple-disk-completion-family-strictly-paid"
                                                for r in results),
        "remaining_selected_unpaid_families": sum(r["status"] == "unpaid" for r in results),
        "results": results, "source_sha256": sha(Path(__file__)),
        "parent_catalog_sha256": source["groups_sha256"],
        "all_other_parent_groups_not_paid_here": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
