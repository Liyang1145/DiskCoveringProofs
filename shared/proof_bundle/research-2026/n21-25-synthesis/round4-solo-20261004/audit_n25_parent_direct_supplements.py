"""Complete-source incremental strict supplements for accepted B16/B17 parents."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, unchanged
from batch_origin_collar import parent_gate, catalog_rows
from audit_complete_origin_finer_supplement import valid_payment_partition, full_filling_source
from audit_complete_origin_finer_with_direct import add_family
from linked_general_collar_kernel import replay as replay_filling

assert __debug__


def accept_base(base, snapshot):
    assert base["verified"] and (base["N"], base["B"]) == (snapshot["N"], snapshot["B"])
    assert base["N"] == 25 and base["B"] in (16, 17)
    if base["schema"] == "complete-library-parent-gapped-filling-residual-merge-v1":
        assert base["source_sha256"] == sha(ROOT / "audit_library_parent_fillings.py")
        assert base["all_complete_parent_indices_partitioned_once"]
        assert base["all_current_pending_rows_match_genuine_original_snapshot_positions"]
        assert base["all_new_positive_whole_filling_trees_freshly_mathematically_replayed"]
        assert base["previous_accepted_weak_library_parent_and_all_its_bound_bytes_rechecked"]
        assert base["no_original_snapshot_source_or_schema_identity_forged"]
        total = base["complete_parent_weak_graphs"]
    else:
        assert base["schema"] == "complete-origin-parent-fresh-weak-and-filling-merge-v1"
        assert base["source_sha256"] == sha(ROOT / "audit_complete_origin_fillings.py")
        assert base["all_complete_parent_rows_partitioned_once"]
        assert base["all_positive_weak_force_and_filling_trees_freshly_replayed"]
        assert base["all_family_source_faces_exactly_equal_complete_parent_faces"]
        total = base["parent_weak_graphs"]
    assert total == snapshot["parent_weak_graphs"] and 0 < base["remaining_weak_graphs"] <= total
    return total


def check_source(row, collar, payload, recorded, N, B, snapshot_hash, constants_hash):
    assert type(collar["complete_parent_index"]) is int
    assert collar["complete_parent_index"] == row["id"]
    assert collar["source_snapshot_sha256"] == snapshot_hash
    assert (collar["N"], collar["B"], collar["centers"], collar["faces"]) == (
        N, B, row["centers"], row["faces"])
    assert payload["source_collar_sha256"] is not None
    full_filling_source(row, payload, recorded, N, B, constants_hash)


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "base", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--addition", nargs=4, action="append", required=True,
                    metavar=("PARENT", "FAMILY", "PROOF", "EXACT"))
    args = ap.parse_args()
    snapshotpath, basepath, controlpath, output = (
        getattr(args, name).resolve() for name in ("snapshot", "base", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, basepath, controlpath, output))
    assert not output.exists()
    snapshot, base, controls = map(read, (snapshotpath, basepath / "VERIFIED.json", controlpath))
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert snapshot["all_full_parent_pending_rows_frozen_once"]
    assert snapshot["every_pending_parent_row_compared_against_full_catalog"]
    total = accept_base(base, snapshot)
    assert controls["verified"] and controls["schema"] == "N25-B16-B17-direct-parent-incremental-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n25_parent_direct_supplements.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["frozen_deeper_family_checker_sha256"] == sha(ROOT / "audit_complete_origin_finer_with_direct.py")
    files = dict(base["frozen_files"])
    for path, digest in snapshot["frozen_files"].items():
        if path in files:
            assert files[path] == digest
        files[path] = digest
    for path, digest in files.items():
        assert sha(path) == digest
    parent = {key: Path(value) for key, value in snapshot["parent_inputs"].items()}
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    N, B = snapshot["N"], snapshot["B"]
    assert (union["N"], union["B"], union["unique_necessary_weak_graphs"]) == (N, B, total)
    assert sha(basepath / "PAYMENTS.jsonl") == base["payments_sha256"]
    assert sha(basepath / "PENDING.jsonl") == base["pending_sha256"]
    originals = {row["parent_index"]: row for row in snapshot["graphs"]}
    assert len(originals) == len(snapshot["graphs"]) == snapshot["selected_pending_graphs"]
    additions, families = {}, {}
    for pidtext, familytext, prooftext, exacttext in args.addition:
        pid = int(pidtext)
        assert str(pid) == pidtext and pid in originals
        family, proofpath, exactpath = map(lambda value: Path(value).resolve(), (familytext, prooftext, exacttext))
        add_family(additions, pid, family, proofpath, exactpath, files)
        families[pid] = family
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == 25
    assert F(constants["radius_upper"]) == F(239146311738101, 10**15)
    output.mkdir()
    counts, visited, oldpaidcount, oldpendingcount = Counter(), set(), 0, 0
    with (basepath / "PAYMENTS.jsonl").open(encoding="ascii") as oldpaid, \
            (basepath / "PENDING.jsonl").open(encoding="ascii") as oldpending, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as pending:
        partition = valid_payment_partition(total, oldpaid, oldpending)
        for row in catalog_rows(catalogpath, N, B, total):
            pid, payment, unresolved = next(partition)
            assert pid == row["id"]
            if payment is not None:
                assert pid not in additions, "supplement targets an already-paid parent"
                counts["unchanged-accepted-parent-payment"] += 1
                oldpaidcount += 1
            else:
                oldpendingcount += 1
                assert unresolved["not_paid"] and pid in originals
                assert (unresolved["centers"], unresolved["faces"]) == (row["centers"], row["faces"])
                assert (originals[pid]["centers"], originals[pid]["faces"]) == (row["centers"], row["faces"])
                if pid in additions:
                    proofpath, exactpath = additions[pid]
                    collarpath = families[pid] / "INPUT-COLLAR.json"
                    collar, payload, recorded = map(read, (collarpath, proofpath, exactpath))
                    check_source(row, collar, payload, recorded, N, B, sha(snapshotpath), constantshash)
                    assert payload["source_collar_sha256"] == sha(collarpath)
                    result = replay_filling(proofpath, constants)
                    assert result["all_full_simple_disk_completions_strictly_paid"]
                    assert all(recorded[key] == value for key, value in result.items())
                    payment = {"parent_index": pid, "status": "strict-complete-filling-family",
                               "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
                               "not_a_standalone_geometric_weak_graph_exclusion": True}
                    counts["new-strict-direct-family"] += 1
                    visited.add(pid)
                    files[str(collarpath)] = sha(collarpath)
                else:
                    counts["pending"] += 1
                    pending.write(json.dumps(unresolved, separators=(",", ":"))+"\n")
            if payment is not None:
                ledger.write(json.dumps(payment, separators=(",", ":"))+"\n")
        assert next(partition, None) is None
    assert visited == set(additions)
    assert oldpendingcount == base["remaining_weak_graphs"]
    assert oldpaidcount+oldpendingcount == total == sum(counts.values())
    assert counts["new-strict-direct-family"]+counts["pending"] == oldpendingcount
    for path in (Path(__file__), snapshotpath, basepath / "VERIFIED.json", basepath / "PAYMENTS.jsonl",
                 basepath / "PENDING.jsonl", controlpath, constantspath,
                 ROOT / "audit_complete_origin_finer_with_direct.py",
                 ROOT / "audit_complete_origin_finer_supplement.py",
                 ROOT / "linked_general_collar_kernel.py"):
        files[str(path)] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-whole-source-direct-family-strict-increment-v1",
        "N": N, "B": B, "complete_parent_weak_graphs": total,
        "previous_pending_weak_graphs": oldpendingcount,
        "additional_strict_complete_families": len(additions),
        "remaining_weak_graphs": counts["pending"], "counts": dict(counts),
        "all_complete_parent_indices_partitioned_once": True,
        "every_new_whole_filling_tree_freshly_mathematically_replayed": True,
        "all_new_conditional_proofs_require_exact_whole_parent_source_faces": True,
        "only_actual_accepted_parent_pending_indices_paid": True,
        "old_parent_proofs_reused_unchanged_without_claim_of_new_old_tree_replay": True,
        "base_report_sha256": sha(basepath / "VERIFIED.json"),
        "payments_sha256": sha(output / "PAYMENTS.jsonl"), "pending_sha256": sha(output / "PENDING.jsonl"),
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "source_cover_transport_other_families_and_nonstrict_core_cases_still_required": True,
        "global_optimality_proved": False,
    })
    print("N25 whole-parent strict direct supplements accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
