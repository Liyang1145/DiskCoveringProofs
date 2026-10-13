"""Complete-source strict increments plus literal same-root nonstrict transport.

Old accepted tree theorems are unchanged prerequisites. All new strict trees
are mathematically replayed here; the nonstrict transported theorem is reused
under exact whole-source face equality, never as a strict U exclusion.
"""
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
from n25_outer_search import read, publish
from batch_origin_collar import parent_gate, catalog_rows
from audit_complete_origin_finer_supplement import valid_payment_partition
from audit_complete_origin_finer_with_direct import add_family
from audit_n25_parent_direct_supplements import accept_base, check_source
from linked_general_collar_kernel import replay
from audit_n25_attaining_parent_transport import match_parent

assert __debug__


def eligible_parent(pid, already_paid, strict_ids, nonstrict_ids):
    assert type(pid) is int
    assert not (set(strict_ids) & set(nonstrict_ids)), "strict/nonstrict duplicate source parent"
    if already_paid:
        assert pid not in strict_ids and pid not in nonstrict_ids, "supplement targets already-paid source"
        return "unchanged"
    if pid in strict_ids:
        return "strict"
    if pid in nonstrict_ids:
        return "nonstrict"
    return "pending"


def check_transport(row, original, transport, candidate, snapshash):
    assert transport["verified"]
    assert transport["schema"] == "N25-literal-whole-parent-nonstrict-completion-theorem-transport-v1"
    assert (transport["N"], transport["B"], transport["complete_parent_weak_graphs"]) == (25, 16, 120782)
    assert transport["source_sha256"] == sha(ROOT / "audit_n25_attaining_parent_transport.py")
    assert transport["actual_complete_parent_source_row_and_genuine_original_pending_snapshot_matched"]
    assert transport["entire_parent_outer_faces_literally_equal_not_proper_subgraph_or_count_only"]
    assert transport["all_simple_hole_completions_freshly_reenumerated_without_node_budget"]
    assert transport["old90_strict_and311883_node_core_math_theorem_reused_unchanged_not_fresh_replay_claim"]
    assert transport["not_a_strict_upper_radius_exclusion_of_the_attaining_parent"]
    assert transport["source_snapshot_sha256"] == snapshash
    assert transport["parent_index"] == row["id"]
    assert (transport["centers"], transport["faces"]) == (row["centers"], row["faces"])
    assert (transport["full_completion_types"], transport["strict_completion_types"],
            transport["nonstrict_same_root_core_completion_types"], transport["pending_completions"]) == (91, 90, 1, 0)
    assert transport["core_lower_radius"] == candidate["core_lower_radius"] == "1/(sqrt(6)+sqrt(3))"
    match_parent(row, original, candidate, 25, 16)


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "base", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--addition", nargs=4, action="append", default=[],
                    metavar=("PARENT", "FAMILY", "PROOF", "EXACT"))
    ap.add_argument("--nonstrict", nargs=2, action="append", required=True,
                    metavar=("TRANSPORT", "CANDIDATE"))
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
    assert (snapshot["N"], snapshot["B"], total) == (25, 16, 120782)
    assert controls["verified"] and controls["schema"] == "N25-whole-parent-mixed-payment-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n25_parent_mixed_supplements.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["strict_checker_sha256"] == sha(ROOT / "audit_n25_parent_direct_supplements.py")
    assert controls["nonstrict_checker_sha256"] == sha(ROOT / "audit_n25_attaining_parent_transport.py")
    files = dict(base["frozen_files"])
    for path, digest in snapshot["frozen_files"].items():
        assert path not in files or files[path] == digest
        files[path] = digest
    originals = {row["parent_index"]: row for row in snapshot["graphs"]}
    assert len(originals) == len(snapshot["graphs"]) == snapshot["selected_pending_graphs"]
    additions, families, transports = {}, {}, {}
    for pidtext, familytext, prooftext, exacttext in args.addition:
        pid = int(pidtext)
        assert str(pid) == pidtext and pid in originals
        family, proofpath, exactpath = map(lambda v: Path(v).resolve(), (familytext, prooftext, exacttext))
        add_family(additions, pid, family, proofpath, exactpath, files)
        families[pid] = family
    for transporttext, candidatetext in args.nonstrict:
        transportpath, candidatepath = Path(transporttext).resolve(), Path(candidatetext).resolve()
        assert transportpath.is_relative_to(ROOT) and candidatepath.is_relative_to(ROOT)
        transport, candidate = read(transportpath), read(candidatepath)
        pid = transport["parent_index"]
        assert type(pid) is int and pid in originals and pid not in transports and pid not in additions
        assert transport["candidate_theorem_sha256"] == sha(candidatepath)
        assert candidate["source_sha256"] == sha(ROOT / "close_candidate_collar.py")
        assert transport["parent_to_completions_sha256"] == sha(transportpath.parent / "PARENT-TO-COMPLETIONS.json")
        for path, digest in transport["frozen_files"].items():
            assert path not in files or files[path] == digest
            files[path] = digest
        for path in (transportpath, candidatepath, transportpath.parent / "PARENT-TO-COMPLETIONS.json"):
            files[str(path)] = sha(path)
        transports[pid] = transportpath, candidatepath, transport, candidate
    for path, digest in files.items():
        assert sha(path) == digest
    parent = {key: Path(value) for key, value in snapshot["parent_inputs"].items()}
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    assert (union["N"], union["B"], union["unique_necessary_weak_graphs"]) == (25, 16, total)
    assert sha(basepath / "PAYMENTS.jsonl") == base["payments_sha256"]
    assert sha(basepath / "PENDING.jsonl") == base["pending_sha256"]
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == 25
    assert F(constants["radius_upper"]) == F(239146311738101, 10**15)
    output.mkdir()
    counts, seenstrict, seennonstrict, oldpending = Counter(), set(), set(), 0
    with (basepath / "PAYMENTS.jsonl").open(encoding="ascii") as oldpaid, \
            (basepath / "PENDING.jsonl").open(encoding="ascii") as unresolved, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        partition = valid_payment_partition(total, oldpaid, unresolved)
        for row in catalog_rows(catalogpath, 25, 16, total):
            pid, payment, pending = next(partition)
            assert pid == row["id"]
            route = eligible_parent(pid, payment is not None, additions, transports)
            if payment is not None:
                counts["unchanged-accepted-parent-payment"] += 1
            else:
                oldpending += 1
                assert pending["not_paid"] and pid in originals
                assert (pending["centers"], pending["faces"]) == (row["centers"], row["faces"])
                assert (originals[pid]["centers"], originals[pid]["faces"]) == (row["centers"], row["faces"])
                if route == "strict":
                    proofpath, exactpath = additions[pid]
                    collarpath = families[pid] / "INPUT-COLLAR.json"
                    collar, payload, recorded = map(read, (collarpath, proofpath, exactpath))
                    check_source(row, collar, payload, recorded, 25, 16, sha(snapshotpath), constantshash)
                    assert payload["source_collar_sha256"] == sha(collarpath)
                    result = replay(proofpath, constants)
                    assert result["all_full_simple_disk_completions_strictly_paid"]
                    assert all(recorded[key] == value for key, value in result.items())
                    payment = {
                        "parent_index": pid, "status": "strict-complete-filling-family",
                        "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
                        "not_a_standalone_geometric_weak_graph_exclusion": True,
                    }
                    counts["new-strict-complete-family"] += 1
                    seenstrict.add(pid)
                    files[str(collarpath)] = sha(collarpath)
                elif route == "nonstrict":
                    transportpath, candidatepath, transport, candidate = transports[pid]
                    check_transport(row, originals[pid], transport, candidate, sha(snapshotpath))
                    payment = {
                        "parent_index": pid, "status": "nonstrict-same-root-complete-family",
                        "transport_sha256": sha(transportpath), "candidate_theorem_sha256": sha(candidatepath),
                        "core_lower_radius": candidate["core_lower_radius"],
                        "strict_completion_types": 90, "same_root_core_completion_types": 1,
                        "not_a_strict_upper_radius_weak_graph_exclusion": True,
                    }
                    counts["new-nonstrict-same-root-complete-family"] += 1
                    seennonstrict.add(pid)
                else:
                    assert route == "pending"
                    counts["pending"] += 1
                    residual.write(json.dumps(pending, separators=(",", ":"))+"\n")
            if payment is not None:
                ledger.write(json.dumps(payment, separators=(",", ":"))+"\n")
        assert next(partition, None) is None
    assert seenstrict == set(additions) and seennonstrict == set(transports)
    assert oldpending == base["remaining_weak_graphs"]
    assert counts["new-strict-complete-family"]+counts["new-nonstrict-same-root-complete-family"]+counts["pending"] == oldpending
    assert sum(counts.values()) == total
    for path in (Path(__file__), snapshotpath, basepath / "VERIFIED.json", basepath / "PAYMENTS.jsonl",
                 basepath / "PENDING.jsonl", controlpath, constantspath,
                 ROOT / "audit_n25_parent_direct_supplements.py",
                 ROOT / "audit_n25_attaining_parent_transport.py", ROOT / "linked_general_collar_kernel.py"):
        files[str(path)] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-whole-parent-strict-and-same-root-family-payment-v1",
        "N": 25, "B": 16, "complete_parent_weak_graphs": total,
        "previous_pending_weak_graphs": oldpending, "counts": dict(counts),
        "remaining_weak_graphs": counts["pending"],
        "complete_necessary_family_lower_payments_closed": counts["pending"] == 0,
        "all_complete_parent_source_indices_disjointly_partitioned_once": True,
        "all_new_strict_whole_family_trees_freshly_mathematically_replayed": True,
        "nonstrict_theorem_requires_literal_whole_source_face_equality_and_actual91_type_transport": True,
        "attaining_parent_not_recast_as_a_strict_upper_radius_exclusion": True,
        "old_parent_and_nonstrict_math_theorems_reused_unchanged_not_fresh_old_tree_replays": True,
        "base_report_sha256": sha(basepath / "VERIFIED.json"),
        "payments_sha256": sha(output / "PAYMENTS.jsonl"), "pending_sha256": sha(output / "PENDING.jsonl"),
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "other_necessary_families_arbitrary_cover_reduction_and_global_same_root_assembly_still_required": True,
        "global_optimality_proved": False,
    })
    print("N25 entire B16 mixed strict/same-root parent payment accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
