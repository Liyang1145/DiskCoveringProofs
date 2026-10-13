"""Fresh all-row union of finite slab sparse payments and exact filling families."""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import validate
from linked_general_collar_kernel import replay as replay_branch
from family_sparse_gate import sparse_library_gate
from n25_outer_search import read, publish, bind, unchanged
from closed_origin_slab import rows, ledger_header

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for key in ("payments", "snapshot", "fillings", "refinement", "controls", "output"):
        ap.add_argument("--"+key, type=Path, required=True)
    args = ap.parse_args()
    for key in vars(args):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists()
    parent_path = args.payments / "VERIFIED.json"
    parent, proposal = read(parent_path), read(args.payments / "PROPOSAL.json")
    assert parent["verified"] and parent["schema"] == "independent-finite-origin-slab-sparse-partition-v1"
    assert parent["source_sha256"] == sha(ROOT / "replay_closed_origin_slab.py")
    assert parent["proposal_sha256"] == sha(args.payments / "PROPOSAL.json")
    assert parent["not_a_complete_competitor_family_or_union"]
    unchanged(parent["files_relative_to_workspace"])
    snapshot = read(args.snapshot)
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    assert snapshot["not_a_complete_competitor_family_or_union"]
    assert snapshot["source_slab_sha256"] == parent["source_slab_sha256"]
    fillings_path, refinement_path = args.fillings / "VERIFIED.json", args.refinement / "VERIFIED.json"
    fillings, refinement = read(fillings_path), read(refinement_path)
    assert fillings["verified"] and fillings["schema"] == "finite-discovery-linked-filling-payments-v1"
    assert fillings["source_snapshot_sha256"] == sha(args.snapshot)
    assert fillings["source_sha256"] == sha(ROOT / "pay_finite_discovery_fillings.py")
    assert refinement["verified"] and refinement["schema"] == "finite-linked-filling-complete-leaf-refinement-v1"
    assert refinement["source_stage_sha256"] == sha(fillings_path)
    assert refinement["source_sha256"] == sha(ROOT / "refine_finite_linked_fillings.py")
    unchanged(fillings["files_relative_to_workspace"])
    unchanged(refinement["files_relative_to_workspace"])
    controls = read(args.controls)
    assert controls["verified"] and controls["schema"] == "linked-general-collar-filling-controls-v1"
    assert controls["all_no_payment_complete_type_sets_equal_to_references"]
    assert controls["known_attaining_candidate_not_strictly_paid"]
    assert controls["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
    assert controls["provider_sha256"] == sha(ROOT / "general_collar_filling_linked.py")
    assert controls["source_induction_sha256"] == sha(ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md")
    unchanged(controls["files_relative_to_workspace"])
    N, B, slab_index = parent["N"], parent["B"], parent["slab_index"]
    assert (snapshot["N"], snapshot["B"]) == (fillings["N"], fillings["B"]) == (
        refinement["N"], refinement["B"]) == (N, B)
    assert N == 25 and B in (15, 16, 17)
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    files = dict(parent["files_relative_to_workspace"])
    selected = {}
    by_sample = {row["sample"]: row for row in fillings["outcomes"]}
    assert len(by_sample) == len(fillings["outcomes"]) == fillings["finite_pending_samples_processed_once"]
    source_pending_ids = {row["sample"] for row in fillings["outcomes"] if row["status"] == "pending"}
    refined_ids = {row["sample"] for row in refinement["outcomes"]}
    assert len(refined_ids) == len(refinement["outcomes"]) and refined_ids <= source_pending_ids
    sources = []
    for row in fillings["outcomes"]:
        if row["status"] == "strictly-paid-complete-filling-family":
            family = args.fillings / f"sample-{row['sample']:07}"
            sources.append((row, family / "PROPOSAL.json", family / "EXACT.json"))
    for row in refinement["outcomes"]:
        if row["status"] == "strictly-paid-refined-complete-filling-family":
            family = args.refinement / f"sample-{row['sample']:07}"
            sources.append((row, family / "REFINED.json", family / "EXACT.json"))
    proof_results = []
    for row, proof_path, exact_path in sources:
        sample = row["sample"]
        assert sample not in selected
        assert sha(proof_path) == row["proposal_sha256"] and sha(exact_path) == row["exact_sha256"]
        recorded = read(exact_path)
        assert recorded["verified"] and recorded["all_full_simple_disk_completions_strictly_paid"]
        payload = read(proof_path)
        assert payload["constants_sha256"] == sha(constants_path)
        assert payload["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
        checked = replay_branch(proof_path, constants)
        assert all(recorded[key] == value for key, value in checked.items())
        assert checked["all_full_simple_disk_completions_strictly_paid"]
        assert checked["pending_complete_leaves"] == checked["unsearched_frontier_nodes"] == 0
        graph = snapshot["weak_graphs"][sample]
        assert (checked["N"], checked["B"], checked["collar_centers"], checked["collar_faces"]) == (
            N, B, graph["centers"], graph["faces"])
        position = snapshot["selected_source_positions"][sample]["slab_row"]
        selected[sample] = {"sample": sample, "slab_row": position, **graph,
                            "proof_sha256": sha(proof_path), "exact_sha256": sha(exact_path)}
        proof_results.append({"sample": sample, "slab_row": position, **checked})
        bind(files, proof_path);bind(files, exact_path)
    by_row = {row["slab_row"]: row for row in selected.values()}
    assert len(by_row) == len(selected)
    library_path = ROOT / proposal["library_relative_to_round4"]
    _, library, table, library_files = sparse_library_gate(library_path)
    files.update(library_files)
    obstacles = {row["id"]: row for row in library["obstacles"]}
    source_slab = ROOT / proposal["source_slab_relative_to_round4"]
    assert sha(source_slab) == parent["source_slab_sha256"]
    ledger_path = args.payments / "PARTITION.jsonl"
    assert sha(ledger_path) == parent["partition_sha256"]
    args.output.mkdir()
    combined_path, pending_path = args.output / "PARTITION.jsonl", args.output / "PENDING.jsonl"
    counts, found, overlaps = Counter(), set(), 0
    with ledger_path.open(encoding="ascii") as old, combined_path.open("x", encoding="ascii") as combined, \
            pending_path.open("x", encoding="ascii") as pending:
        assert json.loads(next(old), object_pairs_hook=no_duplicate_keys) == ledger_header(N, B, slab_index)
        new_header = {"schema": "finite-origin-slab-sparse-and-filling-ledger-v1", "N": N, "B": B,
                      "slab_index": slab_index, "not_a_complete_competitor_family_or_union": True}
        for stream in (combined, pending):
            stream.write(json.dumps(new_header, separators=(",", ":"))+"\n")
        for index, graph in rows(source_slab, B, slab_index):
            entry = json.loads(next(old), object_pairs_hook=no_duplicate_keys)
            assert entry["slab_row"] == index and (entry["centers"], entry["faces"]) == (
                graph["centers"], graph["faces"])
            supplemental = by_row.get(index)
            if supplemental is not None:
                assert (supplemental["centers"], supplemental["faces"]) == (graph["centers"], graph["faces"])
                found.add(index)
            if entry["status"] == "strict-sparse-injection":
                obstacle = obstacles[entry["obstacle"]]
                assert len(entry["map"]["centers"]) == obstacle["centers"]
                validate(graph["centers"], B, obstacle["faces"], entry["map"], graph["faces"])
                overlaps += supplemental is not None
            else:
                assert entry["status"] == "pending" and entry["no_match_is_not_an_exclusion"]
                if supplemental is not None:
                    entry = {"slab_row": index, **graph, "status": "strict-complete-filling-family",
                             "source_sample": supplemental["sample"],
                             "proof_sha256": supplemental["proof_sha256"],
                             "exact_sha256": supplemental["exact_sha256"],
                             "not_a_standalone_geometric_weak_graph_exclusion": True}
                else:
                    pending.write(json.dumps(entry, separators=(",", ":"))+"\n")
            counts[entry["status"]] += 1
            combined.write(json.dumps(entry, separators=(",", ":"))+"\n")
        assert not old.read().strip()
    assert found == set(by_row) and sum(counts.values()) == parent["finite_rows_fully_scanned"] == 100000
    assert counts["strict-sparse-injection"] == parent["strictly_paid_rows"]
    assert counts["strict-complete-filling-family"]+overlaps == len(selected)
    for path in (Path(__file__), parent_path, args.snapshot, fillings_path, refinement_path,
                 args.controls, constants_path, ROOT / "linked_general_collar_kernel.py",
                 ROOT / "general_collar_filling.py", ROOT / "general_collar_filling_linked.py",
                 ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md", source_slab, ledger_path, library_path):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath",
                                                   "pay_finite_discovery_fillings", "refine_finite_linked_fillings"))
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "independent-finite-origin-slab-combined-payments-v1",
        "N": N, "B": B, "slab_index": slab_index, "finite_rows_fully_scanned": 100000,
        "strict_sparse_rows": counts["strict-sparse-injection"],
        "additional_complete_filling_family_rows": counts["strict-complete-filling-family"],
        "supplemental_families_already_sparse_paid": overlaps,
        "total_paid_rows": 100000-counts["pending"], "pending_rows": counts["pending"],
        "freshly_replayed_complete_filling_families": len(selected), "filling_replay_results": proof_results,
        "all_source_rows_partitioned_once_and_overlap_removed": True,
        "all_sparse_injections_and_complete_filling_trees_fresh_replayed": True,
        "source_slab_sha256": sha(source_slab), "partition_sha256": sha(combined_path),
        "pending_sha256": sha(pending_path), "files_relative_to_workspace": files,
        "source_sha256": sha(Path(__file__)), "not_a_complete_competitor_family_or_union": True,
        "slab_row_numbers_not_final_union_ids": True, "global_optimality_proved": False,
    })
    print("Finite slab combined exact acceptance PASS:", 100000-counts["pending"],
          "paid;", counts["pending"], "pending;", overlaps, "overlapping family payments removed", flush=True)


if __name__ == "__main__":
    main()
