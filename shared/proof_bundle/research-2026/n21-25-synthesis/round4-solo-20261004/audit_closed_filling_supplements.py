"""Fresh finite-slab audit of immutable completed conditional filling families.

One-shot extraction from a possibly active larger stage. Only individually
finished independent replays can be used; the whole larger stage is never
treated as finished. Every old and new positive payment is replayed again.
"""
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
from family_sparse_gate import sparse_library_gate
from linked_general_collar_kernel import replay as replay_branch
from n25_outer_search import read, publish, bind, unchanged
from closed_origin_slab import rows

assert __debug__


def unique_bound_path(files, digest, suffix):
    paths = [ROOT.parents[2] / relative for relative, value in files.items()
             if value == digest and relative.endswith(suffix)]
    assert len(paths) == 1, (digest, suffix, len(paths))
    assert sha(paths[0]) == digest
    return paths[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--payments", type=Path, required=True)
    ap.add_argument("--stage", type=Path, required=True)
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--refinement", type=Path, action="append", default=[])
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    for key in ("payments", "stage", "snapshot", "controls", "output"):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists()
    parent_path = args.payments / "VERIFIED.json"
    parent = read(parent_path)
    assert parent["verified"] and parent["schema"] in (
        "independent-finite-origin-slab-force-supplement-v1",
        "independent-finite-origin-slab-closed-filling-supplement-v1")
    parent_script = ("audit_all_finite_slab_strict_supplement.py"
                     if parent["schema"] == "independent-finite-origin-slab-force-supplement-v1"
                     else Path(__file__).name)
    assert parent["source_sha256"] == sha(ROOT / parent_script)
    assert parent["not_a_complete_competitor_family_or_union"]
    unchanged(parent["files_relative_to_workspace"])
    snapshot, stage_inputs, controls = map(read, (
        args.snapshot, args.stage / "INPUT-BINDINGS.json", args.controls))
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    assert snapshot["all_parent_pending_rows_frozen_once"] and snapshot["not_a_complete_competitor_family_or_union"]
    assert snapshot["source_slab_sha256"] == parent["source_slab_sha256"]
    assert stage_inputs["complete_boundary_family_not_claimed"]
    unchanged(stage_inputs["files_relative_to_workspace"])
    assert controls["verified"] and controls["schema"] == "linked-general-collar-filling-controls-v1"
    assert controls["known_attaining_candidate_not_strictly_paid"]
    assert controls["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
    assert controls["provider_sha256"] == sha(ROOT / "general_collar_filling_linked.py")
    assert controls["source_induction_sha256"] == sha(ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md")
    unchanged(controls["files_relative_to_workspace"])
    N, B, slab_index = parent["N"], parent["B"], parent["slab_index"]
    assert (snapshot["N"], snapshot["B"]) == (stage_inputs["N"], stage_inputs["B"]) == (N, B)
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    files = dict(parent["files_relative_to_workspace"])
    proposals = {}
    # A family STATUS is written only after its successful exact process has
    # ended; incomplete final publishing is skipped, never counted as payment.
    for status_path in sorted(args.stage.glob("sample-*/STATUS.json")):
        try:
            status = read(status_path)
        except (ValueError, OSError):
            continue
        if status["status"] != "strictly-paid-complete-filling-family":
            continue
        family = status_path.parent
        terminal_path = family / "REPLAY-TERMINAL.json"
        terminal = read(terminal_path)
        assert terminal["actual_exit_code"] == 0 and terminal["independent_process_terminal_observed"]
        assert terminal["source_sha256"] == sha(ROOT / "replay_linked_general_collar.py")
        proof_path, exact_path = family / "PROPOSAL.json", family / "EXACT.json"
        assert sha(proof_path) == status["proposal_sha256"] and sha(exact_path) == status["exact_sha256"]
        assert status["sample"] not in proposals
        proposals[status["sample"]] = (proof_path, exact_path, status_path)
        bind(files, terminal_path)
    for directory in args.refinement:
        directory = directory.resolve()
        assert directory.is_relative_to(ROOT)
        report_path = directory / "VERIFIED.json"
        report = read(report_path)
        assert report["verified"] and report["schema"] == "frozen-completed-linked-family-leaf-refinement-v1"
        assert report["source_sha256"] == sha(ROOT / "refine_closed_linked_stage_snapshot.py")
        assert report["source_discovery_snapshot_sha256"] == sha(args.snapshot)
        unchanged(report["files_relative_to_workspace"])
        assert len({row["sample"] for row in report["outcomes"]}) == len(report["outcomes"])
        for status in report["outcomes"]:
            if status["status"] != "strictly-paid-refined-complete-filling-family":
                continue
            family = directory / f"sample-{status['sample']:07}"
            proof_path, exact_path, status_path = family / "REFINED.json", family / "EXACT.json", family / "STATUS.json"
            assert sha(proof_path) == status["proposal_sha256"] and sha(exact_path) == status["exact_sha256"]
            assert status["sample"] not in proposals, "a sample is paid twice by two supposedly disjoint refinements"
            proposals[status["sample"]] = (proof_path, exact_path, status_path)
        bind(files, report_path)
    accepted = {}
    for sample, (proof_path, exact_path, status_path) in proposals.items():
        recorded = read(exact_path)
        assert recorded["verified"] and recorded["all_full_simple_disk_completions_strictly_paid"]
        assert recorded["source_sha256"] in (
            sha(ROOT / "replay_linked_general_collar.py"), sha(ROOT / "replay_refined_linked_leaves.py"))
        unchanged(recorded["files_relative_to_workspace"])
        result = replay_branch(proof_path, constants)
        assert all(recorded[key] == value for key, value in result.items())
        assert result["all_full_simple_disk_completions_strictly_paid"]
        graph = snapshot["weak_graphs"][sample]
        assert (result["N"], result["B"], result["collar_centers"], result["collar_faces"]) == (
            N, B, graph["centers"], graph["faces"])
        row_index = snapshot["selected_source_positions"][sample]["slab_row"]
        assert row_index not in accepted
        accepted[row_index] = {"slab_row": row_index, **graph,
                              "status": "strict-complete-filling-family",
                              "source_sample": sample, "proof_sha256": sha(proof_path),
                              "exact_sha256": sha(exact_path),
                              "not_a_standalone_geometric_weak_graph_exclusion": True}
        for path in (proof_path, exact_path, status_path):
            bind(files, path)
    assert accepted
    library_path = ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"
    _, library, _, library_files = sparse_library_gate(library_path)
    files.update(library_files)
    obstacles = {row["id"]: row for row in library["obstacles"]}
    source_slab = unique_bound_path(files, parent["source_slab_sha256"], f".chunk-{slab_index}.jsonl")
    ledger_path, parent_pending_path = args.payments / "PARTITION.jsonl", args.payments / "PENDING.jsonl"
    assert sha(ledger_path) == parent["partition_sha256"] and sha(parent_pending_path) == parent["pending_sha256"]
    args.output.mkdir()
    new_ledger_path, new_pending_path = args.output / "PARTITION.jsonl", args.output / "PENDING.jsonl"
    counts, new_payments, old_overlap, found = Counter(), 0, 0, set()
    with ledger_path.open(encoding="ascii") as source, parent_pending_path.open(encoding="ascii") as old_pending, \
            new_ledger_path.open("x", encoding="ascii") as ledger, new_pending_path.open("x", encoding="ascii") as pending:
        header = json.loads(next(source), object_pairs_hook=no_duplicate_keys)
        assert header["schema"] in ("finite-origin-slab-sparse-filling-and-force-ledger-v1",
                                    "finite-origin-slab-incremental-paid-ledger-v1")
        assert (header["N"], header["B"], header["slab_index"]) == (N, B, slab_index)
        assert json.loads(next(old_pending), object_pairs_hook=no_duplicate_keys) == header
        new_header = {**header, "schema": "finite-origin-slab-incremental-paid-ledger-v1"}
        for stream in (ledger, pending):
            stream.write(json.dumps(new_header, separators=(",", ":"))+"\n")
        for row_index, graph in rows(source_slab, B, slab_index):
            entry = json.loads(next(source), object_pairs_hook=no_duplicate_keys)
            assert entry["slab_row"] == row_index and (entry["centers"], entry["faces"]) == (
                graph["centers"], graph["faces"])
            if row_index in accepted:
                assert (accepted[row_index]["centers"], accepted[row_index]["faces"]) == (
                    graph["centers"], graph["faces"])
                found.add(row_index)
            if entry["status"] == "pending":
                assert json.loads(next(old_pending), object_pairs_hook=no_duplicate_keys) == entry
                if row_index in accepted:
                    entry = accepted[row_index]
                    new_payments += 1
                else:
                    pending.write(json.dumps(entry, separators=(",", ":"))+"\n")
            elif entry["status"] == "strict-sparse-injection":
                obstacle = obstacles[entry["obstacle"]]
                assert len(entry["map"]["centers"]) == obstacle["centers"]
                validate(graph["centers"], B, obstacle["faces"], entry["map"], graph["faces"])
                old_overlap += row_index in accepted
            elif entry["status"] == "strict-whole-weak-force":
                tree_path = unique_bound_path(files, entry["tree_sha256"], ".json.gz")
                with gzip.open(tree_path, "rt", encoding="utf8") as stream:
                    tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
                assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                    N, B, graph["centers"], graph["faces"])
                assert tree["constants_sha256"] == sha(constants_path)
                assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in tree["nodes"])
                result = exact.verify(B, graph["centers"], graph["faces"], tree["nodes"], constants)
                assert result["verified"]
                assert result["minimum_force_margin"] is None or F(result["minimum_force_margin"]) > 0
                old_overlap += row_index in accepted
            else:
                assert entry["status"] == "strict-complete-filling-family"
                proof_path = unique_bound_path(files, entry["proof_sha256"], ".json")
                result = replay_branch(proof_path, constants)
                assert (result["N"], result["B"], result["collar_centers"], result["collar_faces"]) == (
                    N, B, graph["centers"], graph["faces"])
                assert result["all_full_simple_disk_completions_strictly_paid"]
                old_overlap += row_index in accepted
            counts[entry["status"]] += 1
            ledger.write(json.dumps(entry, separators=(",", ":"))+"\n")
        assert not source.read().strip() and not old_pending.read().strip()
    assert sum(counts.values()) == 100000 and found == set(accepted)
    assert new_payments+old_overlap == len(accepted)
    assert 100000-counts["pending"] == parent["total_paid_rows"]+new_payments
    for path in (Path(__file__), parent_path, args.snapshot, args.stage / "INPUT-BINDINGS.json",
                 args.controls, ledger_path, parent_pending_path, source_slab, constants_path,
                 ROOT / "linked_general_collar_kernel.py", HIGH / "exact_graph.py"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "independent-finite-origin-slab-closed-filling-supplement-v1",
        "N": N, "B": B, "slab_index": slab_index, "finite_rows_fully_scanned": 100000,
        "new_complete_filling_family_payments": new_payments, "overlapping_supplemental_payments_removed": old_overlap,
        "source_completed_families_fresh_replayed": len(accepted),
        "total_paid_rows": 100000-counts["pending"], "pending_rows": counts["pending"], "counts": dict(counts),
        "all_old_and_new_positive_payments_fresh_replayed_and_source_rows_checked": True,
        "source_slab_sha256": sha(source_slab), "partition_sha256": sha(new_ledger_path),
        "pending_sha256": sha(new_pending_path), "parent_report_sha256": sha(parent_path),
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    print("Closed finite filling supplements independently accepted:", new_payments,
          "new payments;", old_overlap, "overlaps removed;",
          100000-counts["pending"], "total paid;", counts["pending"], "pending", flush=True)


if __name__ == "__main__":
    main()
