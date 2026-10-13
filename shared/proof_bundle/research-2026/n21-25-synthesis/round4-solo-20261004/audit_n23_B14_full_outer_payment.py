"""Independent full-source adoption of strict trees on the actual B14 residual.

The previous origin/pair payments remain bound prerequisites, not new payments.
No canonicalizer or numerical proposal code is imported by this acceptor.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from paid_binary_residual import BinaryRows
from audit_streamed_hierarchy import check_map
from partition_n23_B14_binary_origin import source_gate, independent_mask
from audit_n23_B15_effective_outer_payment import pending_indices
from n25_outer_search import read, publish
import exact_graph as exact

assert __debug__


def pair_payments(stream, total):
    previous = -1
    for line in stream:
        row = json.loads(line, object_pairs_hook=no_duplicate_keys)
        index = row["index"]
        assert type(index) is int and previous < index < total
        assert type(row["group"]) is int and row["group"] >= 0
        assert type(row["tree_sha256"]) is str and len(row["tree_sha256"]) == 64
        previous = index
        yield row


def scan(rows, old_pairs, old_pending, bindings, groups, paid,
         total, expected, ledger, residual):
    pair = next(old_pairs, None)
    pending = next(old_pending, None)
    counts, members = Counter(), Counter()
    seen = selected = 0
    previous_binding = -1
    started = time.monotonic()
    assert [group["id"] for group in groups] == list(range(len(groups)))
    assert set(paid).issubset(range(len(groups)))
    for index, row in rows:
        assert type(index) is int and index == seen
        seen += 1
        assert len(row["faces"]) == len(set(row["faces"])) == 30
        assert pair is None or pair["index"] >= index
        assert pending is None or type(pending) is int and pending >= index
        mask = independent_mask(row["faces"])
        if mask == (1 << 23)-1:
            assert pair is None or pair["index"] != index
            assert pending != index, "already-origin-paid type reintroduced"
            counts["unchanged-origin-obstruction"] += 1
        elif pair is not None and pair["index"] == index:
            assert pending != index, "already-pair-paid type reintroduced"
            counts["unchanged-strict-pair-type"] += 1
            pair = next(old_pairs, None)
        else:
            assert pending == index, "source row missing from previous disjoint partition"
            selected += 1
            line = bindings.readline()
            assert line, "missing current residual full-outer binding"
            binding = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert type(binding["index"]) is int
            assert binding["index"] == index > previous_binding
            previous_binding = index
            gid = binding["group"]
            assert type(gid) is int and 0 <= gid < len(groups)
            group = groups[gid]
            assert group["centers"] == mask.bit_count() < 23
            check_map(23, 14, group, binding["map"], set(row["faces"]), 1)
            members[gid] += 1
            if gid in paid:
                counts["new-strict-full-outer-type"] += 1
                ledger.write(json.dumps({
                    "index": index, "group": gid, "tree_sha256": paid[gid],
                }, separators=(",", ":"))+"\n")
            else:
                counts["pending"] += 1
                residual.write(json.dumps({"index": index}, separators=(",", ":"))+"\n")
            pending = next(old_pending, None)
        if seen % 250000 == 0:
            print("N23/B14 actual full-outer source-payment scan", seen, "/", total,
                  dict(counts), "seconds", round(time.monotonic()-started, 1), flush=True)
    assert seen == total and selected == expected
    assert pair is pending is None and not bindings.read(1)
    assert all(members[group["id"]] == group["members"] > 0 for group in groups)
    assert sum(counts.values()) == total
    assert counts["new-strict-full-outer-type"]+counts["pending"] == expected
    return dict(counts)


def check_tree(tree, group, outcome, groupshash, constants, constantshash):
    assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
        23, 14, group["centers"], group["faces"])
    assert tree["groups_sha256"] == groupshash
    assert tree["constants_sha256"] == constantshash
    assert tree["radius_upper"] == constants["radius_upper"]
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    result = exact.verify(14, group["centers"], group["faces"], tree["nodes"], constants)
    assert result["verified"] and F(result["minimum_force_margin"]) > 0
    assert result["nodes"] == outcome["nodes"] and result["counts"] == outcome["counts"]
    assert outcome["members"] == group["members"]
    return result


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "parent", "groups", "stage", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    sourcepath, parent, groupspath, stage, controlpath, output = (
        getattr(args, name).resolve()
        for name in ("source", "parent", "groups", "stage", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (
        sourcepath, parent, groupspath, stage, controlpath, output))
    assert not output.exists()
    accepted, data, receipt, replay, terminal, controls, restored = map(read, (
        parent / "VERIFIED.json", groupspath, stage / "SUMMARY.json",
        stage / "EXACT-REPLAY.json", stage / "REPLAY-TERMINAL.json", controlpath,
        groupspath.parent / "RESTORED-SELECTION.json"))
    assert accepted["verified"]
    assert accepted["schema"] == "N23-B14-original-origin-and-fresh-pair-disjoint-payment-v1"
    assert accepted["source_sha256"] == sha(ROOT / "audit_n23_B14_pair_payment.py")
    assert (accepted["N"], accepted["B"], accepted["original_catalog_types"]) == (23, 14, 8277632)
    assert accepted["all_source_indices_original_origin_status_and_actual_pair_maps_independently_scanned"]
    assert accepted["all_21_positive_pair_trees_freshly_exact_replayed_again"]
    assert accepted["old_origin_payments_not_recounted_as_new_strict_types"]
    assert accepted["counts"] == {
        "old-origin-obstruction": 5725962, "new-strict-pair-type": 183487, "pending": 2368183}
    assert accepted["pending_full_types"] == 2368183
    catalogpath, sourcefiles = source_gate(sourcepath)
    frozen = dict(accepted["frozen_files"])
    for path, digest in sourcefiles.items():
        assert path not in frozen or frozen[path] == digest
        frozen[path] = digest
    assert (data["N"], data["B"], data["threshold"]) == (23, 14, 1)
    assert data["catalog_types"] == 8277632 and data["selected_types"] == 2368183
    assert data["catalog_sha256"] == sha(catalogpath)
    assert data["source_sha256"] == sha(ROOT / "group_n23_B14_remaining_outer.py")
    assert data["parent_proof_sha256"] == sha(parent / "VERIFIED.json")
    assert data["parent_groups_sha256"] is None
    assert data["selection_kind"] == "actual-verified-current-source-residual-all-exposed-faces"
    assert data["full_selected_catalog_scanned"] and data["verified_embeddings_during_generation"]
    groups = data["groups"]
    assert [group["id"] for group in groups] == list(range(data["group_count"]))
    assert sum(group["members"] for group in groups) == 2368183
    groupshash = sha(groupspath)
    bindingspath = (groupspath.parent / data["bindings_file"]).resolve()
    assert bindingspath.is_relative_to(ROOT) and sha(bindingspath) == data["bindings_sha256"]
    assert restored["schema"] == "N23-B14-verified-residual-full-outer-restoration-v1"
    assert restored["source_sha256"] == data["source_sha256"]
    assert restored["groups_sha256"] == groupshash
    assert restored["bindings_sha256"] == sha(bindingspath)
    assert restored["actual_selected_residual_types"] == 2368183
    for path, digest in restored["frozen_files"].items():
        assert path not in frozen or frozen[path] == digest
        frozen[path] = digest
    assert controls["verified"]
    assert controls["schema"] == "N23-B14-actual-full-outer-payment-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_B14_full_outer_payment.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["frozen_mapping_checker_sha256"] == sha(HIGH / "audit_streamed_hierarchy.py")
    assert controls["frozen_exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert receipt["source_sha256"] == sha(ROOT / "propose_isolated_small_order_groups.py")
    assert receipt["groups_sha256"] == replay["groups_sha256"] == groupshash
    assert receipt["requested_groups_complete"] and (receipt["N"], receipt["B"]) == (23, 14)
    assert receipt["known_attaining_group_control"] is None
    assert replay["verified"] and replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert (replay["N"], replay["B"]) == (23, 14)
    assert replay["receipt_sha256"] == sha(stage / "SUMMARY.json")
    assert replay["bindings_sha256"] == sha(bindingspath)
    assert terminal["independent_process_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert [row["group"] for row in receipt["outcomes"]] == list(range(len(groups)))
    paid, associated = {}, 0
    for group, outcome in zip(groups, receipt["outcomes"], strict=True):
        assert outcome["status"] in ("excluded", "pending")
        if outcome["status"] == "pending":
            continue
        path = stage / f"group-{group['id']:07}.json.gz"
        assert sha(path) == outcome["tree_sha256"]
        with gzip.open(path, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        check_tree(tree, group, outcome, groupshash, constants, constantshash)
        paid[group["id"]] = sha(path)
        associated += group["members"]
        frozen[str(path)] = sha(path)
        if len(paid) % 1000 == 0:
            print("N23/B14 full-outer trees freshly replayed again", len(paid), flush=True)
    assert len(paid) == receipt["excluded_groups"] == replay["exact_groups_replayed"]
    assert len(groups)-len(paid) == receipt["pending_groups"] == replay["pending_groups"]
    assert associated == receipt["catalog_members_excluded"] == replay["associated_member_count"]
    oldpairspath, oldpendingpath = parent / "ADDITIONAL-PAYMENTS.jsonl", parent / "PENDING.jsonl"
    assert sha(oldpairspath) == accepted["additional_payments_sha256"]
    assert sha(oldpendingpath) == accepted["pending_sha256"]
    for path, digest in receipt["frozen_files"].items():
        assert path not in frozen or frozen[path] == digest
        frozen[path] = digest
    for path in (Path(__file__), sourcepath, parent / "VERIFIED.json", oldpairspath,
                 oldpendingpath, groupspath, bindingspath, controlpath, constantspath,
                 groupspath.parent / "RESTORED-SELECTION.json", stage / "SUMMARY.json",
                 stage / "EXACT-REPLAY.json", stage / "REPLAY-TERMINAL.json",
                 HIGH / "audit_streamed_hierarchy.py", HIGH / "exact_graph.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    catalog = BinaryRows(catalogpath)
    with oldpairspath.open(encoding="ascii") as oldpairs, \
            bindingspath.open(encoding="ascii") as bindings, \
            (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        counts = scan(
            catalog.rows(), pair_payments(oldpairs, 8277632),
            pending_indices(oldpendingpath, 8277632), bindings, groups, paid,
            8277632, 2368183, ledger, residual)
    assert catalog.finished
    assert counts["unchanged-origin-obstruction"] == 5725962
    assert counts["unchanged-strict-pair-type"] == 183487
    assert counts.get("new-strict-full-outer-type", 0) == associated
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-current-residual-full-outer-disjoint-payment-v1",
        "N": 23, "B": 14, "original_catalog_types": 8277632,
        "previous_pending_full_types": 2368183, "counts": counts,
        "additional_strict_full_outer_types": associated,
        "pending_full_types": counts.get("pending", 0), "positive_groups": len(paid),
        "all_source_rows_previous_payment_partition_and_current_full_outer_maps_checked": True,
        "all_new_positive_full_outer_trees_freshly_exact_replayed_again": True,
        "previous_origin_and_pair_proofs_unchanged_bound_prerequisites_not_fresh_old_tree_replays": True,
        "previous_paid_types_not_reintroduced_or_recounted_as_new": True,
        "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "complete_source_induction_actual_cover_interface_and_other_families_still_upstream": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 full-source current full-outer payments accepted:", counts, flush=True)


if __name__ == "__main__":
    main()
