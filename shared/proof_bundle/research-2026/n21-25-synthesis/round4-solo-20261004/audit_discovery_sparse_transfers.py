"""Fresh strict-library acceptance and finite discovery-parent injection audit."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from family_sparse_gate import sparse_library_gate
from n25_outer_search import read, publish, bind, unchanged
from audit_paid_prefix_sparse import audit_transfers, jsonl

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--replay", type=Path, required=True)
    ap.add_argument("--sparse", type=Path, required=True)
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    for key in vars(args):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists()
    snapshot, source_receipt, source_replay = map(read, (args.snapshot, args.receipt, args.replay))
    data, receipt, replay = map(read, (
        args.sparse / "GROUPS.json", args.sparse / "SUMMARY.json", args.sparse / "EXACT-REPLAY.json"))
    constants, library, table, files = sparse_library_gate(args.library)
    assert (snapshot["N"], snapshot["B"]) == (25, library["B"]) == (data["N"], data["B"])
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    assert not snapshot["complete_necessary_outer_search"]
    assert data["not_a_complete_family"] and not data["full_selected_catalog_scanned"]
    assert source_receipt["schema"] == "individually-paid-discovery-graphs-v1"
    assert source_receipt["snapshot_sha256"] == source_replay["snapshot_sha256"] == sha(args.snapshot)
    assert source_replay["verified"] and source_replay["receipt_sha256"] == sha(args.receipt)
    assert source_replay["source_sha256"] == sha(ROOT / "replay_family_discovery.py")
    assert source_replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert source_replay["no_optimizer_imported"]
    assert receipt["source_receipt_sha256"] == sha(args.receipt)
    assert receipt["source_exact_replay_sha256"] == sha(args.replay)
    assert data["catalog_sha256"] == sha(args.snapshot)
    assert receipt["groups_sha256"] == replay["groups_sha256"] == sha(args.sparse / "GROUPS.json")
    assert replay["verified"] and replay["pending_groups"] == receipt["pending_groups"] == 0
    assert library["obstacle_count"] == data["group_count"] == replay["exact_groups_replayed"]
    assert [(g["id"], g["centers"], g["faces"]) for g in data["groups"]] == [
        (o["id"], o["centers"], o["faces"]) for o in library["obstacles"]]
    entries = jsonl(args.sparse / "parent-maps.jsonl")
    bindings = jsonl(args.sparse / data["bindings_file"])
    assert sha(args.sparse / data["bindings_file"]) == data["bindings_sha256"]
    original_ids = [row["parent_discovery_group"] for row in entries]
    assert original_ids == sorted(set(original_ids))
    assert len(source_receipt["outcomes"]) == snapshot["weak_graph_count"] == len(snapshot["weak_graphs"])
    excluded_ids = [row["group"] for row in source_receipt["outcomes"] if row["status"] == "excluded"]
    assert original_ids == excluded_ids
    parents = []
    normalized_entries = []
    for index, entry in enumerate(entries):
        original_id = entry["parent_discovery_group"]
        parent = snapshot["weak_graphs"][original_id]
        outcome = source_receipt["outcomes"][original_id]
        assert outcome["group"] == original_id and outcome["status"] == "excluded"
        assert (parent["centers"], parent["faces"]) == (outcome["centers"], outcome["faces"])
        parents.append({"id": index, **parent})
        normalized_entries.append({
            **{key: value for key, value in entry.items() if key != "parent_discovery_group"},
            "parent_prefix_group": index,
        })
    before, after = audit_transfers(parents, data, normalized_entries, bindings)
    assert before == receipt["parent_face_count"] and after == receipt["reduced_face_count"]
    assert before-after == receipt["accepted_deletions"]
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath",
                                                   "sparsify_family_discovery", "probe_groups"))
    for path in (Path(__file__), ROOT / "audit_paid_prefix_sparse.py", args.snapshot, args.receipt,
                 args.replay, args.library, args.sparse / "GROUPS.json", args.sparse / "SUMMARY.json",
                 args.sparse / "EXACT-REPLAY.json", args.sparse / "parent-maps.jsonl",
                 args.sparse / data["bindings_file"], HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    publish(args.output, {
        "verified": True, "schema": "independent-finite-discovery-sparse-transfers-v1",
        "N": 25, "B": data["B"], "finite_discovery_graph_count": snapshot["weak_graph_count"],
        "strict_parent_count": len(parents), "unpaid_source_samples": source_replay["totals"].get("pending", 0),
        "standalone_strict_obstacles": library["obstacle_count"],
        "all_selected_parent_center_anchor_face_injections_checked": True,
        "all_new_sparse_trees_fresh_exact_replayed": True,
        "no_optimizer_or_sparsification_proposer_imported": True,
        "parent_face_count": before, "retained_face_count": after,
        "source_snapshot_sha256": sha(args.snapshot), "library_sha256": sha(args.library),
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    print("Finite discovery sparse transfers PASS:", len(parents), "parents;",
          library["obstacle_count"], "whole-domain strict obstacles", flush=True)


if __name__ == "__main__":
    main()
