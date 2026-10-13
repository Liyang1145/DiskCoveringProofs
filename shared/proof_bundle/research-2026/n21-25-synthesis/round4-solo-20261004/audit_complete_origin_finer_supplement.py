"""All-parent fresh replay including disjoint finished-family finer proofs.

Requires the primary entire-parent filling audit to have ended. All its old
positive weak trees and complete-filling trees are mathematically replayed
again. New refinements can pay only exact original pending parent indices.
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
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, unchanged
from batch_origin_collar import parent_gate, catalog_rows
from linked_general_collar_kernel import replay as replay_filling
import exact_graph as exact

assert __debug__


def valid_payment_partition(total, paid_stream, pending_stream):
    def row(stream):
        line = stream.readline()
        return json.loads(line, object_pairs_hook=no_duplicate_keys) if line else None
    paid, pending = row(paid_stream), row(pending_stream)
    for index in range(total):
        assert paid is None or paid["parent_index"] >= index
        assert pending is None or pending["parent_index"] >= index
        is_paid = paid is not None and paid["parent_index"] == index
        is_pending = pending is not None and pending["parent_index"] == index
        assert is_paid != is_pending, "missing, overlapping, or duplicated parent payment row"
        if is_paid:
            assert type(paid["parent_index"]) is int
            yield index, paid, None
            paid = row(paid_stream)
        else:
            assert type(pending["parent_index"]) is int
            yield index, None, pending
            pending = row(pending_stream)
    assert paid is pending is None, "extra parent payment or pending rows"


def full_filling_source(row, payload, exact, N, B, constants_hash):
    assert (payload["N"], payload["B"], payload["collar_centers"], payload["collar_faces"]) == (
        N, B, row["centers"], row["faces"]), "conditional proof source graph mismatch"
    assert (exact["N"], exact["B"], exact["collar_centers"], exact["collar_faces"]) == (
        N, B, row["centers"], row["faces"]), "conditional replay source graph mismatch"
    assert payload["constants_sha256"] == constants_hash
    assert payload["source_sha256"] == sha(ROOT / "prove_linked_general_collar.py")
    assert payload["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
    assert exact["verified"] and exact["all_full_simple_disk_completions_strictly_paid"]
    assert exact["source_sha256"] in (
        sha(ROOT / "replay_linked_general_collar.py"), sha(ROOT / "replay_refined_linked_leaves.py"))


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "base", "output", "controls"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--refinement", type=Path, action="append", required=True)
    args = ap.parse_args()
    snapshotpath, basepath, output, controlpath = (getattr(args, name).resolve()
                                                  for name in ("snapshot", "base", "output", "controls"))
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, basepath, output, controlpath))
    assert not output.exists()
    snapshot, base, controls = map(read, (snapshotpath, basepath / "VERIFIED.json", controlpath))
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert base["verified"] and base["schema"] == "complete-origin-parent-fresh-weak-and-filling-merge-v1"
    assert base["source_sha256"] == sha(ROOT / "audit_complete_origin_fillings.py")
    assert base["all_complete_parent_rows_partitioned_once"]
    assert base["all_positive_weak_force_and_filling_trees_freshly_replayed"]
    assert base["all_family_source_faces_exactly_equal_complete_parent_faces"]
    assert (base["N"], base["B"]) == (snapshot["N"], snapshot["B"]) == (25, 15)
    assert controls["verified"] and controls["schema"] == "complete-parent-finer-supplement-finite-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_complete_origin_finer_supplement.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    files = dict(base["frozen_files"])
    for path, digest in files.items():
        assert sha(path) == digest
    parent = {key: Path(value) for key, value in snapshot["parent_inputs"].items()}
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    total, N, B = union["unique_necessary_weak_graphs"], union["N"], union["B"]
    assert total == base["parent_weak_graphs"] == snapshot["parent_weak_graphs"]
    assert sha(basepath / "PAYMENTS.jsonl") == base["payments_sha256"]
    assert sha(basepath / "PENDING.jsonl") == base["pending_sha256"]
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    assert constants["verified"] and constants["N"] == N
    additions = {}
    for reportpath in args.refinement:
        reportpath = reportpath.resolve()
        assert reportpath.is_relative_to(ROOT)
        report = read(reportpath)
        assert report["verified"] and report["schema"] == "finished-complete-origin-pending-leaf-refinement-results-v1"
        assert (report["N"], report["B"]) == (N, B)
        assert report["source_complete_parent_snapshot_sha256"] == sha(snapshotpath)
        assert report["source_sha256"] in (
            sha(ROOT / "refine_finished_complete_origin_pending.py"),
            sha(ROOT / "refine_finished_complete_origin_pending_next.py"))
        assert report["only_original_FULL_PENDING_leaves_changed"]
        assert report["all_old_positive_nodes_and_topological_child_lists_unchanged"]
        assert len(report["outcomes"]) == report["selected_families"]
        for path, digest in report["frozen_files"].items():
            assert sha(path) == digest
        inputs_path = reportpath.parent / "INPUT-SNAPSHOT.json"
        assert sha(inputs_path) == report["input_snapshot_sha256"]
        inputs = read(inputs_path)
        assert inputs["source_complete_parent_snapshot_sha256"] == sha(snapshotpath)
        selected = {row["parent_index"]: row for row in inputs["selected"]}
        assert len(selected) == len(inputs["selected"])
        for status in report["outcomes"]:
            index = status["parent_index"]
            assert type(index) is int and index in selected
            if status["status"] != "strict-complete-filling-family":
                assert status["status"] == "pending"
                continue
            assert index not in additions, "duplicate supposedly disjoint finer-family payment"
            directory = reportpath.parent / f"parent-{index:07}"
            proofpath, exactpath = directory / "REFINED.json", directory / "EXACT.json"
            assert sha(proofpath) == status["proof_sha256"] and sha(exactpath) == status["exact_sha256"]
            family = Path(selected[index]["family"])
            assert family.is_relative_to(ROOT)
            payload = read(proofpath)
            assert payload["original_proposal_sha256"] == sha(family / "PROPOSAL.json")
            assert payload["original_exact_replay_sha256"] == sha(family / "EXACT.json")
            assert payload["refinement_source_sha256"] == sha(ROOT / "refine_linked_collar_leaves.py")
            additions[index] = (selected[index], proofpath, exactpath)
            for path in (proofpath, exactpath, inputs_path):
                files[str(path)] = sha(path)
        files.update(report["frozen_files"])
        files[str(reportpath)] = sha(reportpath)
    assert additions
    assert set(additions) <= {row["parent_index"] for row in snapshot["graphs"]}
    proof_paths = {}
    for path, digest in base["frozen_files"].items():
        filepath = Path(path)
        if filepath.name in ("PROPOSAL.json", "REFINED.json"):
            proof_paths.setdefault(digest, []).append(filepath)
    original_graphs = {
        row["parent_index"]: row for row in snapshot["graphs"]}
    batch_size = read(parent["partition"])["batch_size"]
    output.mkdir()
    counts, seen_extra = Counter(), set()
    with (basepath / "PAYMENTS.jsonl").open(encoding="ascii") as oldpaid, \
            (basepath / "PENDING.jsonl").open(encoding="ascii") as oldpending, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as pending:
        oldrows = valid_payment_partition(total, oldpaid, oldpending)
        for row in catalog_rows(catalogpath, N, B, total):
            index, payment, unresolved = next(oldrows)
            assert index == row["id"]
            if payment is not None:
                assert index not in additions, "extra refinement targets an already-paid parent"
                if payment["status"] == "strict-exact-weak-graph-exclusion":
                    batch, local = divmod(index, batch_size)
                    groupspath = parent["partition"].parent / f"batch-{batch:06}/GROUPS.json"
                    treepath = groupspath.parent / f"PROPOSALS/group-{local:07}.json.gz"
                    assert sha(treepath) == payment["tree_sha256"]
                    with gzip.open(treepath, "rt", encoding="utf8") as stream:
                        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
                    assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                        N, B, row["centers"], row["faces"])
                    assert tree["groups_sha256"] == sha(groupspath) and tree["constants_sha256"] == constantshash
                    assert tree["radius_upper"] == constants["radius_upper"]
                    result = exact.verify(B, row["centers"], row["faces"], tree["nodes"], constants)
                    assert result["verified"] and F(result["minimum_force_margin"]) > 0
                    assert str(F(result["minimum_force_margin"])) == payment["minimum_force_margin"]
                    files[str(treepath)] = payment["tree_sha256"]
                    files[str(groupspath)] = tree["groups_sha256"]
                    counts["strict-weak-force"] += 1
                else:
                    assert payment["status"] == "strict-complete-filling-family"
                    candidates = proof_paths[payment["proof_sha256"]]
                    assert len(candidates) == 1
                    proofpath = candidates[0]
                    payload = read(proofpath)
                    assert (payload["N"], payload["B"], payload["collar_centers"], payload["collar_faces"]) == (
                        N, B, row["centers"], row["faces"])
                    assert payload["constants_sha256"] == constantshash
                    assert payload["source_sha256"] == sha(ROOT / "prove_linked_general_collar.py")
                    assert payload["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
                    result = replay_filling(proofpath, constants)
                    assert result["all_full_simple_disk_completions_strictly_paid"]
                    assert sha(proofpath) == payment["proof_sha256"]
                    counts["old-strict-complete-filling-family"] += 1
            else:
                assert (unresolved["centers"], unresolved["faces"]) == (row["centers"], row["faces"])
                assert unresolved["not_paid"] and index in original_graphs
                if index in additions:
                    selected, proofpath, exactpath = additions[index]
                    assert (selected["centers"], selected["faces"]) == (row["centers"], row["faces"])
                    payload, recorded = read(proofpath), read(exactpath)
                    full_filling_source(row, payload, recorded, N, B, constantshash)
                    unchanged(recorded["files_relative_to_workspace"])
                    result = replay_filling(proofpath, constants)
                    assert result["all_full_simple_disk_completions_strictly_paid"]
                    assert all(recorded[key] == value for key, value in result.items())
                    payment = {"parent_index": index, "status": "strict-complete-filling-family",
                               "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
                               "not_a_standalone_geometric_weak_graph_exclusion": True}
                    seen_extra.add(index)
                    counts["new-strict-finer-complete-filling-family"] += 1
                else:
                    counts["pending"] += 1
                    pending.write(json.dumps(unresolved, separators=(",", ":"))+"\n")
            if payment is not None:
                ledger.write(json.dumps(payment, separators=(",", ":"))+"\n")
            if (index+1) % 5000 == 0:
                print("Complete-parent old/new proofs freshly reaccepted", index+1, "/", total,
                      dict(counts), flush=True)
        assert next(oldrows, None) is None
    assert seen_extra == set(additions)
    assert counts["strict-weak-force"] == base["strict_weak_graph_payments"]
    assert counts["old-strict-complete-filling-family"] == base["strict_complete_filling_family_payments"]
    assert counts["new-strict-finer-complete-filling-family"]+counts["pending"] == base["remaining_weak_graphs"]
    assert sum(counts.values()) == total
    for path in (Path(__file__).resolve(), snapshotpath, basepath / "VERIFIED.json",
                 basepath / "PAYMENTS.jsonl", basepath / "PENDING.jsonl", controlpath, constants_path):
        files[str(path)] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-origin-parent-fresh-finer-supplement-merge-v1",
        "N": N, "B": B, "complete_parent_weak_graphs": total, "counts": dict(counts),
        "remaining_weak_graphs": counts["pending"],
        "all_residual_weak_lower_bounds_paid": counts["pending"] == 0,
        "all_parent_indices_disjointly_partitioned_once": True,
        "every_old_and_new_positive_tree_freshly_mathematically_replayed": True,
        "complete_outer_source_faces_exactly_equal_every_parent_graph": True,
        "new_refinements_pay_only_old_exact_pending_indices": True,
        "payments_sha256": sha(output / "PAYMENTS.jsonl"), "pending_sha256": sha(output / "PENDING.jsonl"),
        "base_report_sha256": sha(basepath / "VERIFIED.json"),
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "conditional_completions_not_standalone_weak_graph_geometry": True,
        "all_other_boundary_families_cover_transport_and_exact_upper_still_required": True,
        "global_optimality_proved": False,
    })
    print("Complete-parent finer supplement independently accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
