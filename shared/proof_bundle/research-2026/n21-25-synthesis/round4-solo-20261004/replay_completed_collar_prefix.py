"""Stdlib-only replay of a completed force-output prefix from a complete catalog.

The live proposer is never modified. A copied prefix is explicitly not a
whole-stage receipt, and pending numeric diagnostics never pay a lower bound.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, unchanged
from batch_streamed_collar import identity

assert __debug__


def replay(catalog, stage, count, output):
    assert 1 <= count <= 50000 and not output.exists()
    summary, terminal = map(read, (catalog / "SUMMARY.json", catalog / "NATIVE-TERMINAL.json"))
    assert summary["verified"] and summary["complete_necessary_outer_collar_overapproximation"]
    assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
    unchanged(summary["files_relative_to_workspace"])
    groupspath = catalog / "GROUPS.json"
    digest = sha(groupspath)
    assert digest == summary["groups_sha256"] and groupspath.stat().st_size <= 128*1024**2
    # This path is intentionally limited to the already-completed 100MB old
    # catalog. Multi-million streaming catalogs use the separate batch tools.
    data = read(groupspath)
    N, B = data["N"], data["B"]
    assert N == 25 and (summary["N"], summary["B"]) == (N, B)
    total = data["group_count"]
    assert len(data["groups"]) == total == data["catalog_types"] == summary["unpaid_weak_graphs"]
    assert data["full_selected_catalog_scanned"] and data["selected_types"] == total
    assert data["members_are_necessary_weak_graphs_not_full_types"]
    assert count <= total
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == N
    bindingpath = catalog / data["bindings_file"]
    bindinghash = sha(bindingpath)
    assert bindinghash == data["bindings_sha256"]
    outcomes = []
    with (stage / "outcomes.jsonl").open(encoding="utf8") as stream:
        for local in range(count):
            line = stream.readline()
            assert line.endswith("\n"), "requested output prefix not fully published yet"
            outcome = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert outcome["group"] == local and outcome["status"] in ("excluded", "pending")
            outcomes.append(outcome)
    output.mkdir()
    snapshot = output / "OUTCOME-PREFIX.jsonl"
    with snapshot.open("x", encoding="ascii") as stream:
        for row in outcomes:
            stream.write(json.dumps(row, separators=(",", ":"))+"\n")
    accepted = 0
    minimum = None
    node_counts = Counter()
    trees, pendingpath = output / "ACCEPTED-TREES.jsonl", output / "PENDING.jsonl"
    with bindingpath.open(encoding="utf8") as bindings, trees.open("x", encoding="ascii") as ledger, \
            pendingpath.open("x", encoding="ascii") as pending:
        for gid, outcome in enumerate(outcomes):
            group = data["groups"][gid]
            assert group["id"] == gid and group["members"] == 1
            binding = json.loads(next(bindings), object_pairs_hook=no_duplicate_keys)
            assert binding == {"index": gid, "group": gid, "map": identity(group["centers"], B)}
            if outcome["status"] == "pending":
                pending.write(json.dumps({"group": gid, "centers": group["centers"],
                                          "faces": group["faces"], "not_an_exclusion": True},
                                         separators=(",", ":"))+"\n")
                continue
            treepath = stage / f"group-{gid:07}.json.gz"
            assert sha(treepath) == outcome["tree_sha256"]
            with gzip.open(treepath, "rt", encoding="utf8") as stream:
                tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
            assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                N, B, group["centers"], group["faces"])
            assert tree["groups_sha256"] == digest and tree["constants_sha256"] == constantshash
            assert tree["radius_upper"] == constants["radius_upper"]
            result = exact.verify(B, group["centers"], group["faces"], tree["nodes"], constants)
            assert result["verified"] and result["nodes"] == outcome["nodes"]
            assert result["counts"] == outcome["counts"] and outcome["members"] == 1
            margin = F(result["minimum_force_margin"])
            assert margin > 0 and sha(treepath) == outcome["tree_sha256"]
            minimum = margin if minimum is None else min(minimum, margin)
            node_counts.update(result["counts"])
            ledger.write(json.dumps({"group": gid, "tree_sha256": outcome["tree_sha256"],
                                     "minimum_force_margin": str(margin),
                                     "identity_into_complete_parent_catalog_checked": True},
                                    separators=(",", ":"))+"\n")
            accepted += 1
            if accepted % 1000 == 0:
                print("Independent completed-prefix exact trees replayed:", accepted, flush=True)
    assert sha(groupspath) == digest and sha(bindingpath) == bindinghash
    assert sha(constantspath) == constantshash
    unchanged(summary["files_relative_to_workspace"])
    result = {
        "verified": True, "schema": "completed-collar-force-prefix-exact-replay-v1", "N": N, "B": B,
        "original_complete_necessary_weak_catalog_size": total,
        "selected_prefix_count": count, "strictly_excluded_weak_graphs": accepted,
        "pending_prefix_weak_graphs": count-accepted,
        "whole_force_stage_receipt_not_claimed": True, "not_the_entire_catalog_lower_bound": True,
        "all_selected_strict_trees_fresh_exact_replayed": True,
        "all_selected_parent_identity_maps_checked": True,
        "minimum_force_margin": None if minimum is None else str(minimum), "node_counts": dict(node_counts),
        "groups_sha256": digest, "bindings_sha256": bindinghash,
        "source_catalog_summary_sha256": sha(catalog / "SUMMARY.json"),
        "source_native_terminal_sha256": sha(catalog / "NATIVE-TERMINAL.json"),
        "outcome_prefix_sha256": sha(snapshot), "accepted_tree_ledger_sha256": sha(trees),
        "pending_sha256": sha(pendingpath), "constants_sha256": constantshash,
        "exact_checker_sha256": sha(HIGH / "exact_graph.py"),
        "proposer_source_sha256": sha(HIGH / "probe_groups.py"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    }
    publish(output / "VERIFIED.json", result)
    return result


def main():
    ap = argparse.ArgumentParser()
    for name in ("catalog", "stage", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--count", type=int, required=True)
    args = ap.parse_args()
    result = replay(args.catalog.resolve(), args.stage.resolve(), args.count, args.output.resolve())
    print("Independent finite prefix paid:", result["strictly_excluded_weak_graphs"], "strict;",
          result["pending_prefix_weak_graphs"], "pending; not whole-catalog closure", flush=True)


if __name__ == "__main__":
    main()
