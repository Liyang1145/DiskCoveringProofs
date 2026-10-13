"""Fresh strict-force replay and exact all-row integration of an entire slab residual."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from group_catalog import validate
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
from linked_general_collar_kernel import replay as replay_family
from closed_origin_slab import rows

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for key in ("payments", "stage", "output"):
        ap.add_argument("--"+key, type=Path, required=True)
    args = ap.parse_args()
    for key in vars(args):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists()
    parent_path = args.payments / "VERIFIED.json"
    parent = read(parent_path)
    assert parent["verified"] and parent["schema"] == "independent-finite-origin-slab-combined-payments-v1"
    assert parent["source_sha256"] == sha(ROOT / "audit_finite_slab_filling_supplement.py")
    assert parent["not_a_complete_competitor_family_or_union"]
    unchanged(parent["files_relative_to_workspace"])
    snapshot_path, receipt_path, replay_path = (
        args.stage / name for name in ("ALL-PENDING-SNAPSHOT.json", "STRICT/SUMMARY.json", "STRICT-EXACT.json"))
    snapshot, receipt, replay = map(read, (snapshot_path, receipt_path, replay_path))
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    assert snapshot["all_parent_pending_rows_frozen_once"] and snapshot["not_a_complete_competitor_family_or_union"]
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_combined_slab_pending.py")
    assert snapshot["source_verified_sha256"] == sha(parent_path)
    assert snapshot["source_pending_sha256"] == parent["pending_sha256"]
    assert receipt["schema"] == "individually-paid-discovery-graphs-v1"
    snapshot_sha = sha(snapshot_path)
    assert receipt["snapshot_sha256"] == replay["snapshot_sha256"] == snapshot_sha
    assert receipt["source_sha256"] == sha(ROOT / "probe_family_discovery.py")
    assert receipt["source_make_sha256"] == sha(HIGH / "probe_groups.py")
    assert replay["verified"] and replay["receipt_sha256"] == sha(receipt_path)
    assert replay["source_sha256"] == sha(ROOT / "replay_family_discovery.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py") and replay["no_optimizer_imported"]
    N, B, slab_index = parent["N"], parent["B"], parent["slab_index"]
    assert (snapshot["N"], snapshot["B"]) == (receipt["N"], receipt["B"]) == (N, B)
    count = snapshot["weak_graph_count"]
    assert count == len(snapshot["weak_graphs"]) == len(receipt["outcomes"]) == parent["pending_rows"]
    assert len(snapshot["selected_source_positions"]) == count
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert receipt["constants_sha256"] == replay["constants_sha256"] == sha(constants_path)
    files = dict(parent["files_relative_to_workspace"])
    totals, accepted = Counter(), {}
    for index, (graph, outcome, position) in enumerate(zip(
            snapshot["weak_graphs"], receipt["outcomes"], snapshot["selected_source_positions"], strict=True)):
        assert outcome["group"] == index and outcome["status"] in ("excluded", "pending")
        assert position["pending_position"] == index
        assert (graph["centers"], graph["faces"]) == (outcome["centers"], outcome["faces"])
        totals[outcome["status"]] += 1
        if outcome["status"] == "pending":
            continue
        tree_path = receipt_path.parent / f"discovered-{index:07}.json.gz"
        assert sha(tree_path) == outcome["tree_sha256"]
        with gzip.open(tree_path, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
            N, B, graph["centers"], graph["faces"])
        assert tree["discovery_snapshot_sha256"] == snapshot_sha
        assert tree["constants_sha256"] == sha(constants_path) and tree["radius_upper"] == constants["radius_upper"]
        assert tree["does_not_assert_family_coverage"]
        assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in tree["nodes"])
        checked = exact.verify(B, graph["centers"], graph["faces"], tree["nodes"], constants)
        assert all(outcome[key] == value for key, value in checked.items())
        assert checked["minimum_force_margin"] is None or F(checked["minimum_force_margin"]) > 0
        row_index = position["slab_row"]
        assert row_index not in accepted
        accepted[row_index] = {"source_sample": index, "tree_sha256": sha(tree_path)}
        bind(files, tree_path)
    assert dict(totals) == receipt["totals"] == replay["totals"]
    # Reaccept every previous conditional filling tree as well as the sparse
    # library. Reopening the old report alone is not a new all-row audit.
    prior_family_by_row = {}
    for previous in parent["filling_replay_results"]:
        sample, row_index = previous["sample"], previous["slab_row"]
        strict_family = ROOT / "n25-B16-finite-pending57-linked-fillings-20261005-v1" / f"sample-{sample:07}"
        refined_family = ROOT / "n25-B16-finite-pending52-linked-force31-20261005-v1" / f"sample-{sample:07}"
        family_proof = (refined_family / "REFINED.json" if refined_family.exists()
                        else strict_family / "PROPOSAL.json")
        result = replay_family(family_proof, constants)
        assert all(previous[key] == value for key, value in result.items())
        assert result["all_full_simple_disk_completions_strictly_paid"]
        prior_family_by_row[row_index] = family_proof
        bind(files, family_proof)
    library_path = ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"
    _, library, _, library_files = sparse_library_gate(library_path)
    files.update(library_files)
    by_id = {row["id"]: row for row in library["obstacles"]}
    source_candidates = [relative for relative, digest in files.items()
                         if digest == parent["source_slab_sha256"] and relative.endswith(f".chunk-{slab_index}.jsonl")]
    assert len(source_candidates) == 1
    source_slab = ROOT.parents[2] / source_candidates[0]
    parent_ledger_path, parent_pending_path = args.payments / "PARTITION.jsonl", args.payments / "PENDING.jsonl"
    assert sha(parent_ledger_path) == parent["partition_sha256"] and sha(parent_pending_path) == parent["pending_sha256"]
    args.output.mkdir()
    ledger_path, pending_path = args.output / "PARTITION.jsonl", args.output / "PENDING.jsonl"
    seen_pending, final_counts = 0, Counter()
    with parent_ledger_path.open(encoding="ascii") as old, parent_pending_path.open(encoding="ascii") as old_pending, \
            ledger_path.open("x", encoding="ascii") as ledger, pending_path.open("x", encoding="ascii") as residual:
        header = {"schema": "finite-origin-slab-sparse-and-filling-ledger-v1", "N": N, "B": B,
                  "slab_index": slab_index, "not_a_complete_competitor_family_or_union": True}
        assert json.loads(next(old), object_pairs_hook=no_duplicate_keys) == header
        assert json.loads(next(old_pending), object_pairs_hook=no_duplicate_keys) == header
        new_header = {**header, "schema": "finite-origin-slab-sparse-filling-and-force-ledger-v1"}
        for stream in (ledger, residual):
            stream.write(json.dumps(new_header, separators=(",", ":"))+"\n")
        for row_index, graph in rows(source_slab, B, slab_index):
            entry = json.loads(next(old), object_pairs_hook=no_duplicate_keys)
            assert entry["slab_row"] == row_index and (entry["centers"], entry["faces"]) == (
                graph["centers"], graph["faces"])
            if entry["status"] == "pending":
                assert json.loads(next(old_pending), object_pairs_hook=no_duplicate_keys) == entry
                assert snapshot["selected_source_positions"][seen_pending]["slab_row"] == row_index
                assert snapshot["weak_graphs"][seen_pending] == graph
                outcome = receipt["outcomes"][seen_pending]
                if row_index in accepted:
                    assert outcome["status"] == "excluded"
                    entry = {"slab_row": row_index, **graph, "status": "strict-whole-weak-force", **accepted[row_index]}
                else:
                    assert outcome["status"] == "pending"
                    residual.write(json.dumps(entry, separators=(",", ":"))+"\n")
                seen_pending += 1
            elif entry["status"] == "strict-sparse-injection":
                obstacle = by_id[entry["obstacle"]]
                assert len(entry["map"]["centers"]) == obstacle["centers"]
                validate(graph["centers"], B, obstacle["faces"], entry["map"], graph["faces"])
            else:
                assert entry["status"] == "strict-complete-filling-family"
                assert row_index in prior_family_by_row and sha(prior_family_by_row[row_index]) == entry["proof_sha256"]
            final_counts[entry["status"]] += 1
            ledger.write(json.dumps(entry, separators=(",", ":"))+"\n")
        assert not old.read().strip() and not old_pending.read().strip()
    assert seen_pending == count
    assert sum(final_counts.values()) == 100000
    assert final_counts["strict-whole-weak-force"] == totals["excluded"]
    assert final_counts["pending"] == totals["pending"]
    assert final_counts["strict-sparse-injection"] == parent["strict_sparse_rows"]
    assert final_counts["strict-complete-filling-family"] == parent["additional_complete_filling_family_rows"]
    for path in (Path(__file__), parent_path, snapshot_path, receipt_path, replay_path, constants_path,
                 source_slab, parent_ledger_path, parent_pending_path, library_path, HIGH / "exact_graph.py",
                 ROOT / "linked_general_collar_kernel.py"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "independent-finite-origin-slab-force-supplement-v1",
        "N": N, "B": B, "slab_index": slab_index, "finite_rows_fully_scanned": 100000,
        "new_strict_force_rows": totals["excluded"], "total_paid_rows": 100000-totals["pending"],
        "pending_rows": totals["pending"], "counts": dict(final_counts),
        "all_parent_pending_rows_compared_with_snapshot_and_proof_outcomes_once": True,
        "all_old_sparse_maps_old_filling_trees_and_new_force_trees_fresh_replayed": True,
        "source_slab_sha256": sha(source_slab), "partition_sha256": sha(ledger_path),
        "pending_sha256": sha(pending_path), "source_parent_report_sha256": sha(parent_path),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    print("ALL finite slab strict supplement independently accepted:",
          totals["excluded"], "new strict;", 100000-totals["pending"], "total paid;",
          totals["pending"], "pending", flush=True)


if __name__ == "__main__":
    main()
