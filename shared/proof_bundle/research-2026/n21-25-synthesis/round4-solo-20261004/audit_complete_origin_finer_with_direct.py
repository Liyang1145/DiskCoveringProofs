"""All-parent fresh replay, including explicit standalone deeper refinements.

The original batch supplement auditor and its controls remain unchanged.
An explicit deeper proof is accepted only against its exact frozen old family,
the old pending parent index, and a fresh mathematical whole-tree replay.
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
from audit_complete_origin_finer_supplement import valid_payment_partition, full_filling_source
from linked_general_collar_kernel import replay as replay_filling
import exact_graph as exact

assert __debug__


def add_family(additions, parent_index, family, proofpath, exactpath, files):
    assert type(parent_index) is int and parent_index not in additions
    assert all(path.is_relative_to(ROOT) for path in (family, proofpath, exactpath))
    oldpath, oldexactpath = family / "PROPOSAL.json", family / "EXACT.json"
    old, payload, accepted = map(read, (oldpath, proofpath, exactpath))
    assert payload["original_proposal_sha256"] == sha(oldpath)
    assert payload["original_exact_replay_sha256"] == sha(oldexactpath)
    assert payload["refinement_source_sha256"] == sha(ROOT / "refine_linked_collar_leaves.py")
    assert accepted["verified"] and accepted["whole_tree_fresh_exact_replayed"]
    assert accepted["source_sha256"] == sha(ROOT / "replay_refined_linked_leaves.py")
    assert accepted["all_full_simple_disk_completions_strictly_paid"]
    assert accepted["pending_complete_leaves"] == accepted["unsearched_frontier_nodes"] == 0
    assert accepted["files_relative_to_workspace"][proofpath.relative_to(ROOT.parents[2]).as_posix()] == sha(proofpath)
    unchanged(accepted["files_relative_to_workspace"])
    for field in ("schema", "N", "B", "collar_centers", "collar_faces", "roots", "constants_sha256",
                  "source_collar_sha256", "kernel_sha256", "source_sha256"):
        assert payload[field] == old[field]
    assert len(payload["nodes"]) == len(old["nodes"])
    changed = []
    for index, (a, b) in enumerate(zip(old["nodes"], payload["nodes"], strict=True)):
        if a != b:
            assert a["kind"] == "FULL_PENDING" and b["state"] == a["state"]
            assert b["kind"] in ("FORCE", "ANGLE")
            changed.append(index)
    assert changed == payload["refined_leaf_indices"]
    additions[parent_index] = (proofpath, exactpath)
    for path in (oldpath, oldexactpath, proofpath, exactpath):
        files[str(path)] = sha(path)


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "base", "controls", "direct-controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--refinement", type=Path, action="append", required=True)
    ap.add_argument("--direct-parent", type=int, required=True)
    for name in ("direct-family", "direct-proof", "direct-exact"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    snapshotpath, basepath, controlpath, directcontrolpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("snapshot", "base", "controls", "direct-controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, basepath, controlpath, directcontrolpath, output))
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
    assert controls["audit_source_sha256"] == sha(ROOT / "audit_complete_origin_finer_supplement.py")
    directcontrols = read(directcontrolpath)
    assert directcontrols["verified"] and directcontrols["schema"] == "standalone-deeper-finer-family-controls-v1"
    assert directcontrols["audit_source_sha256"] == sha(Path(__file__))
    assert directcontrols["source_sha256"] == sha(ROOT / "test_complete_origin_direct_finer.py")
    files = dict(base["frozen_files"])
    for path, digest in {**files, **snapshot["frozen_files"]}.items():
        assert sha(path) == digest
    parent = {key: Path(value) for key, value in snapshot["parent_inputs"].items()}
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    total, N, B = union["unique_necessary_weak_graphs"], union["N"], union["B"]
    assert total == base["parent_weak_graphs"] == snapshot["parent_weak_graphs"]
    assert sha(basepath / "PAYMENTS.jsonl") == base["payments_sha256"]
    assert sha(basepath / "PENDING.jsonl") == base["pending_sha256"]
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants, constantshash = read(constants_path), sha(constants_path)
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
        for path, digest in report["frozen_files"].items():
            assert sha(path) == digest
            files[path] = digest
        inputpath = reportpath.parent / "INPUT-SNAPSHOT.json"
        assert sha(inputpath) == report["input_snapshot_sha256"]
        inputs = read(inputpath)
        selected = {row["parent_index"]: row for row in inputs["selected"]}
        assert len(selected) == len(inputs["selected"]) == report["selected_families"] == len(report["outcomes"])
        for status in report["outcomes"]:
            pid = status["parent_index"]
            assert pid in selected
            if status["status"] == "pending":
                continue
            assert status["status"] == "strict-complete-filling-family"
            directory = reportpath.parent / f"parent-{pid:07}"
            proofpath, exactpath = directory / "REFINED.json", directory / "EXACT.json"
            assert sha(proofpath) == status["proof_sha256"] and sha(exactpath) == status["exact_sha256"]
            add_family(additions, pid, Path(selected[pid]["family"]).resolve(), proofpath, exactpath, files)
        for path in (inputpath, reportpath):
            files[str(path)] = sha(path)
    add_family(additions, args.direct_parent, args.direct_family.resolve(),
               args.direct_proof.resolve(), args.direct_exact.resolve(), files)
    original = {row["parent_index"]: row for row in snapshot["graphs"]}
    assert set(additions) <= set(original)
    oldproofs = {}
    for path, digest in base["frozen_files"].items():
        if Path(path).name in ("PROPOSAL.json", "REFINED.json"):
            oldproofs.setdefault(digest, []).append(Path(path))
    batch_size = read(parent["partition"])["batch_size"]
    output.mkdir()
    counts, seen = Counter(), set()
    with (basepath / "PAYMENTS.jsonl").open(encoding="ascii") as oldpaid, \
            (basepath / "PENDING.jsonl").open(encoding="ascii") as oldpending, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as pending:
        partition = valid_payment_partition(total, oldpaid, oldpending)
        for row in catalog_rows(catalogpath, N, B, total):
            pid, payment, unresolved = next(partition)
            assert pid == row["id"]
            if payment is not None:
                assert pid not in additions
                if payment["status"] == "strict-exact-weak-graph-exclusion":
                    batch, local = divmod(pid, batch_size)
                    groupspath = parent["partition"].parent / f"batch-{batch:06}/GROUPS.json"
                    treepath = groupspath.parent / f"PROPOSALS/group-{local:07}.json.gz"
                    assert sha(treepath) == payment["tree_sha256"]
                    with gzip.open(treepath, "rt", encoding="utf8") as source:
                        tree = json.load(source, object_pairs_hook=no_duplicate_keys)
                    assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                        N, B, row["centers"], row["faces"])
                    if str(groupspath) not in files:
                        files[str(groupspath)] = sha(groupspath)
                    assert tree["groups_sha256"] == files[str(groupspath)]
                    assert tree["constants_sha256"] == constantshash and tree["radius_upper"] == constants["radius_upper"]
                    result = exact.verify(B, row["centers"], row["faces"], tree["nodes"], constants)
                    assert result["verified"] and F(result["minimum_force_margin"]) > 0
                    assert str(F(result["minimum_force_margin"])) == payment["minimum_force_margin"]
                    files[str(treepath)] = payment["tree_sha256"]
                    counts["old-strict-weak-force"] += 1
                else:
                    assert payment["status"] == "strict-complete-filling-family"
                    paths = oldproofs[payment["proof_sha256"]]
                    assert len(paths) == 1
                    payload = read(paths[0])
                    assert (payload["N"], payload["B"], payload["collar_centers"], payload["collar_faces"]) == (
                        N, B, row["centers"], row["faces"])
                    assert payload["constants_sha256"] == constantshash
                    assert payload["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
                    result = replay_filling(paths[0], constants)
                    assert result["all_full_simple_disk_completions_strictly_paid"]
                    counts["old-strict-complete-filling-family"] += 1
            else:
                assert pid in original and unresolved["not_paid"]
                assert (unresolved["centers"], unresolved["faces"]) == (row["centers"], row["faces"])
                if pid in additions:
                    proofpath, exactpath = additions[pid]
                    payload, recorded = read(proofpath), read(exactpath)
                    full_filling_source(row, payload, recorded, N, B, constantshash)
                    result = replay_filling(proofpath, constants)
                    assert result["all_full_simple_disk_completions_strictly_paid"]
                    assert all(recorded[key] == value for key, value in result.items())
                    payment = {"parent_index": pid, "status": "strict-complete-filling-family",
                               "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
                               "not_a_standalone_geometric_weak_graph_exclusion": True}
                    counts["new-strict-finer-complete-filling-family"] += 1
                    seen.add(pid)
                else:
                    counts["pending"] += 1
                    pending.write(json.dumps(unresolved, separators=(",", ":"))+"\n")
            if payment is not None:
                ledger.write(json.dumps(payment, separators=(",", ":"))+"\n")
            if (pid+1) % 5000 == 0:
                print("B15 full-parent old/batch/direct proofs freshly replayed", pid+1, "/", total,
                      dict(counts), flush=True)
        assert next(partition, None) is None
    assert seen == set(additions)
    assert counts["old-strict-weak-force"] == base["strict_weak_graph_payments"]
    assert counts["old-strict-complete-filling-family"] == base["strict_complete_filling_family_payments"]
    assert counts["new-strict-finer-complete-filling-family"]+counts["pending"] == base["remaining_weak_graphs"]
    assert sum(counts.values()) == total
    for path in (Path(__file__), snapshotpath, basepath / "VERIFIED.json", controlpath, directcontrolpath,
                 basepath / "PAYMENTS.jsonl", basepath / "PENDING.jsonl",
                 ROOT / "audit_complete_origin_finer_supplement.py", constants_path,
                 HIGH / "exact_graph.py", Path(exact.kernel.__file__)):
        files[str(path.resolve())] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-origin-parent-fresh-batch-and-direct-finer-merge-v1",
        "N": N, "B": B, "complete_parent_weak_graphs": total, "counts": dict(counts),
        "remaining_weak_graphs": counts["pending"], "all_residual_weak_lower_bounds_paid": counts["pending"] == 0,
        "all_parent_indices_disjointly_partitioned_once": True,
        "every_old_and_new_positive_tree_freshly_mathematically_replayed": True,
        "complete_outer_source_faces_exactly_equal_every_parent_graph": True,
        "new_refinements_pay_only_old_exact_pending_indices": True,
        "direct_refinement_old_positive_nodes_and_topology_recompared": True,
        "payments_sha256": sha(output / "PAYMENTS.jsonl"), "pending_sha256": sha(output / "PENDING.jsonl"),
        "base_report_sha256": sha(basepath / "VERIFIED.json"), "frozen_files": files,
        "source_sha256": sha(Path(__file__)), "conditional_completions_not_standalone_weak_graph_geometry": True,
        "source_cover_transport_other_boundary_families_and_exact_upper_still_required": True,
        "global_optimality_proved": False,
    })
    print("B15 batch plus direct finer supplement independently accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
