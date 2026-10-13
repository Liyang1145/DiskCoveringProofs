"""Fresh full-parent weak-force and conditional whole-filling payment merge."""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, unchanged
from batch_origin_collar import parent_gate, catalog_rows
from audit_origin_collar_batches import audit as audit_roots
from linked_general_collar_kernel import replay as replay_filling

assert __debug__


def match_family_source(row, collar, payload, N, B, digest):
    assert (collar["N"], collar["B"], collar["centers"], collar["faces"]) == (
        N, B, row["centers"], row["faces"]), "collar/complete-parent graph mismatch"
    assert collar["complete_parent_index"] == row["parent_index"], "wrong complete-parent index"
    assert collar["source_snapshot_sha256"] == digest, "wrong parent snapshot binding"
    assert (payload["N"], payload["B"], payload["collar_centers"], payload["collar_faces"]) == (
        N, B, row["centers"], row["faces"]), "proof/complete-parent graph mismatch"


def audit(snapshotpath, stage, controls, output):
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, stage, controls, output))
    assert not output.exists()
    snapshot, jobs, inputs, tested = map(read, (
        snapshotpath, stage / "SUMMARY.json", stage / "INPUT-BINDINGS.json", controls))
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert snapshot["all_full_parent_pending_rows_frozen_once"]
    assert jobs["scheduler_completed"] and jobs["schema"] == "complete-parent-pending-filling-jobs-v1"
    assert jobs["source_sha256"] == sha(ROOT / "pay_complete_origin_pending.py")
    digest = sha(snapshotpath)
    assert jobs["snapshot_sha256"] == inputs["snapshot_sha256"] == digest
    assert jobs["processed_graphs"] == snapshot["selected_pending_graphs"] == len(snapshot["graphs"])
    assert jobs["completed_batches_sha256"] == sha(stage / "COMPLETED-BATCHES.jsonl")
    N, B = snapshot["N"], snapshot["B"]
    assert N == 25 and B in (14, 15, 16, 17)
    assert (jobs["N"], jobs["B"]) == (inputs["N"], inputs["B"]) == (N, B)
    assert tested["verified"] and tested["schema"] == "linked-general-collar-filling-controls-v1"
    assert tested["known_attaining_candidate_not_strictly_paid"]
    assert tested["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
    assert tested["provider_sha256"] == sha(ROOT / "general_collar_filling_linked.py")
    assert tested["source_induction_sha256"] == sha(ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md")
    unchanged(tested["files_relative_to_workspace"])
    files = dict(snapshot["frozen_files"])
    files.update(inputs["frozen_files"])
    for path, expected in files.items():
        assert sha(path) == expected
    parent = {key: Path(value) for key, value in snapshot["parent_inputs"].items()}
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    assert (union["N"], union["B"], union["unique_necessary_weak_graphs"]) == (
        N, B, snapshot["parent_weak_graphs"])
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constantshash = sha(constants_path)
    descriptors = {}
    with (stage / "COMPLETED-BATCHES.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            first = descriptor["first"]
            assert type(first) is int and first not in descriptors
            descriptors[first] = descriptor
    outcomes = {}
    counts = Counter()
    first = 0
    for first_index in sorted(descriptors):
        assert first_index == first, "filling worker selection gap or duplication"
        descriptor = descriptors[first_index]
        reportpath = stage / f"batch-{first_index//inputs['worker_batch_size']:06}/SUMMARY.json"
        worker = read(reportpath)
        assert sha(reportpath) == descriptor["worker_report_sha256"]
        assert worker["schema"] == "complete-parent-pending-filling-worker-v1"
        assert worker["source_sha256"] == sha(ROOT / "pay_complete_origin_pending.py")
        assert worker["snapshot_sha256"] == digest
        assert worker["first"] == first and worker["count"] == len(worker["outcomes"]) == descriptor["count"]
        assert worker["count"] > 0
        assert Counter(row["status"] for row in worker["outcomes"]) == descriptor["counts"]
        for path, expected in worker["frozen_files"].items():
            assert sha(path) == expected
        for local, status in enumerate(worker["outcomes"]):
            graph = snapshot["graphs"][first+local]
            assert (status["parent_index"], status["centers"], status["faces"]) == (
                graph["parent_index"], graph["centers"], graph["faces"])
            assert status["status"] in ("pending", "strict-complete-filling-family")
            index = graph["parent_index"]
            assert index not in outcomes
            outcomes[index] = (status, reportpath.parent)
            counts[status["status"]] += 1
        first += descriptor["count"]
        files[str(reportpath)] = sha(reportpath)
    assert first == len(snapshot["graphs"])
    assert counts == jobs["counts"]
    output.mkdir()
    # Every prior positive root tree is reaccepted, not copied from counts.
    rootreport = audit_roots(parent["manifest"], parent["terminal"], parent["union"],
                            parent["partition"], output / "ROOTS-FRESH-REPLAY")
    assert rootreport["pending_weak_graphs"] == len(snapshot["graphs"])
    freshrootpath = output / "ROOTS-FRESH-REPLAY"
    accepted_families = {}
    for index in sorted(outcomes):
        status, directory = outcomes[index]
        if status["status"] != "strict-complete-filling-family":
            continue
        family = directory / f"parent-{index:07}"
        collarpath = family / "INPUT-COLLAR.json"
        proofpath = (directory / status["proof_relative_to_stage"]).resolve()
        exactpath = (directory / status["exact_relative_to_stage"]).resolve()
        assert proofpath.is_relative_to(family) and exactpath.is_relative_to(family)
        assert sha(proofpath) == status["proof_sha256"] and sha(exactpath) == status["exact_sha256"]
        collar, payload, recorded = map(read, (collarpath, proofpath, exactpath))
        match_family_source(status, collar, payload, N, B, digest)
        assert payload["source_collar_sha256"] == sha(collarpath)
        assert payload["constants_sha256"] == constantshash
        assert payload["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
        assert payload["source_sha256"] == sha(ROOT / "prove_linked_general_collar.py")
        assert recorded["verified"] and recorded["all_full_simple_disk_completions_strictly_paid"]
        assert recorded["source_sha256"] in (
            sha(ROOT / "replay_linked_general_collar.py"), sha(ROOT / "replay_refined_linked_leaves.py"))
        unchanged(recorded["files_relative_to_workspace"])
        result = replay_filling(proofpath, constants)
        assert all(recorded[key] == value for key, value in result.items())
        assert result["all_full_simple_disk_completions_strictly_paid"]
        accepted_families[index] = {
            "parent_index": index, "status": "strict-complete-filling-family",
            "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
            "not_a_standalone_geometric_weak_graph_exclusion": True,
        }
        for path in (collarpath, proofpath, exactpath):
            files[str(path)] = sha(path)
        if len(accepted_families) % 250 == 0:
            print("Whole conditional filling trees freshly accepted", len(accepted_families), flush=True)
    total = union["unique_necessary_weak_graphs"]
    paid = residual = strict = filling = 0
    with (freshrootpath / "PAYMENTS.jsonl").open(encoding="ascii") as roots, \
            (freshrootpath / "PENDING.jsonl").open(encoding="ascii") as oldpending, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as pending:
        for row in catalog_rows(catalogpath, N, B, total):
            index = row["id"]
            if index not in outcomes:
                payment = json.loads(next(roots), object_pairs_hook=no_duplicate_keys)
                assert payment["parent_index"] == index
                assert payment["status"] == "strict-exact-weak-graph-exclusion"
                strict += 1
            else:
                selected = json.loads(next(oldpending), object_pairs_hook=no_duplicate_keys)
                assert selected["parent_index"] == index
                assert (selected["centers"], selected["faces"]) == (row["centers"], row["faces"])
                status, _ = outcomes[index]
                assert (status["centers"], status["faces"]) == (row["centers"], row["faces"])
                payment = accepted_families.get(index)
                if payment is None:
                    pending.write(json.dumps({"parent_index": index, "centers": row["centers"],
                                              "faces": row["faces"], "not_paid": True},
                                             separators=(",", ":"))+"\n")
                    residual += 1
                else:
                    filling += 1
            if payment is not None:
                ledger.write(json.dumps(payment, separators=(",", ":"))+"\n")
                paid += 1
        assert not roots.read(1) and not oldpending.read(1)
    assert strict == rootreport["strictly_excluded"]
    assert filling == len(accepted_families) and total == paid+residual == strict+filling+residual
    for path in (
        Path(__file__).resolve(), snapshotpath, stage / "SUMMARY.json", controls,
        stage / "INPUT-BINDINGS.json", stage / "COMPLETED-BATCHES.jsonl", constants_path,
        ROOT / "linked_general_collar_kernel.py", ROOT / "general_collar_filling_linked.py",
        ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md", freshrootpath / "VERIFIED.json"):
        files[str(path)] = sha(path)
    for path, expected in files.items():
        assert sha(path) == expected
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-origin-parent-fresh-weak-and-filling-merge-v1",
        "N": N, "B": B, "parent_weak_graphs": total,
        "strict_weak_graph_payments": strict, "strict_complete_filling_family_payments": filling,
        "paid_weak_graphs": paid, "remaining_weak_graphs": residual,
        "all_complete_parent_rows_partitioned_once": True,
        "all_positive_weak_force_and_filling_trees_freshly_replayed": True,
        "all_family_source_faces_exactly_equal_complete_parent_faces": True,
        "all_residual_weak_lower_bounds_paid": residual == 0,
        "payments_sha256": sha(output / "PAYMENTS.jsonl"), "pending_sha256": sha(output / "PENDING.jsonl"),
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "conditional_fillings_not_standalone_weak_graph_geometry": True,
        "arbitrary_cover_reduction_other_boundary_families_and_exact_upper_still_required": True,
        "global_optimality_proved": False,
    })
    print("Complete-parent fresh payment merge:", paid, "paid;", residual, "pending", flush=True)


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "stage", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    audit(*(getattr(args, name).resolve() for name in ("snapshot", "stage", "controls", "output")))


if __name__ == "__main__":
    main()
