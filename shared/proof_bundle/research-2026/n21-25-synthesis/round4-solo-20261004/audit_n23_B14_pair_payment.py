"""Fresh exact pair trees and complete original-source map/payment partition."""
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
from partition_n23_B14_binary_origin import source_gate, independent_mask, header
from n25_outer_search import read, publish
import exact_graph as exact

assert __debug__


def scan(rows, origin, bindings, groups, paid, digest, total, expected, ledger, residual):
    assert json.loads(next(origin), object_pairs_hook=no_duplicate_keys) == header(
        "not-paid-by-origin-condition", digest)
    members, counts = Counter(), Counter()
    seen, selected = 0, 0
    previous = -1
    started = time.monotonic()
    for index, row in rows:
        assert index == seen
        seen += 1
        mask = independent_mask(row["faces"])
        if mask == (1 << 23)-1:
            counts["old-origin-obstruction"] += 1
        else:
            selected += 1
            original = json.loads(next(origin), object_pairs_hook=no_duplicate_keys)
            assert original == {"index": index, "exposed_mask": mask}
            line = bindings.readline()
            assert line, "missing actual residual group binding"
            binding = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert type(binding["index"]) is int and binding["index"] == index > previous
            previous = index
            gid = binding["group"]
            assert type(gid) is int and 0 <= gid < len(groups)
            check_map(23, 14, groups[gid], binding["map"], set(row["faces"]), 2)
            members[gid] += 1
            if gid in paid:
                counts["new-strict-pair-type"] += 1
                ledger.write(json.dumps({"index": index, "group": gid,
                                         "tree_sha256": paid[gid]}, separators=(",", ":"))+"\n")
            else:
                counts["pending"] += 1
                residual.write(json.dumps({"index": index}, separators=(",", ":"))+"\n")
        if seen % 250000 == 0:
            print("N23/B14 original pair-payment source scan", seen, "/", total,
                  dict(counts), "seconds", round(time.monotonic()-started, 1), flush=True)
    assert seen == total and selected == expected
    assert not origin.read(1) and not bindings.read(1)
    assert all(members[group["id"]] == group["members"] for group in groups)
    assert sum(counts.values()) == total
    assert counts["new-strict-pair-type"]+counts["pending"] == expected
    return dict(counts)


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "origin", "groups", "stage", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    sourcepath, originpath, groupspath, stage, controlpath, output = (
        getattr(args, name).resolve()
        for name in ("source", "origin", "groups", "stage", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (sourcepath, originpath, groupspath, stage, controlpath, output))
    assert not output.exists()
    catalogpath, frozen = source_gate(sourcepath)
    accepted, data, receipt, replay, terminal, controls = map(read, (
        originpath, groupspath, stage / "SUMMARY.json", stage / "EXACT-REPLAY.json",
        stage / "REPLAY-TERMINAL.json", controlpath))
    assert accepted["verified"] and accepted["schema"] == "independent-complete-original-N23-B14-origin-partition-v1"
    assert accepted["source_sha256"] == sha(ROOT / "partition_n23_B14_binary_origin.py")
    assert accepted["source_report_sha256"] == sha(sourcepath)
    assert accepted["source_types"] == 8277632 and accepted["pending_types"] == 2551670
    assert accepted["catalog_sha256"] == sha(catalogpath)
    assert data["source_sha256"] == sha(ROOT / "group_n23_B14_origin_residual.py")
    assert (data["N"], data["B"], data["threshold"], data["group_count"]) == (23, 14, 2, 381)
    assert data["selected_types"] == 2551670 and data["catalog_types"] == 8277632
    assert data["catalog_sha256"] == sha(catalogpath)
    assert data["parent_proof_sha256"] == sha(originpath)
    assert data["selection_kind"] == "actual-complete-origin-residual-not-whole-catalog"
    assert data["full_selected_catalog_scanned"]
    assert [group["id"] for group in data["groups"]] == list(range(381))
    assert controls["verified"] and controls["schema"] == "N23-B14-actual-pair-payment-source-map-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_B14_pair_payment.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    digest = sha(groupspath)
    bindingspath = (groupspath.parent / data["bindings_file"]).resolve()
    assert bindingspath.is_relative_to(ROOT) and sha(bindingspath) == data["bindings_sha256"]
    assert receipt["source_sha256"] == sha(ROOT / "propose_isolated_small_order_groups.py")
    assert receipt["groups_sha256"] == replay["groups_sha256"] == digest
    assert receipt["requested_groups_complete"] and (receipt["N"], receipt["B"]) == (23, 14)
    assert receipt["known_attaining_group_control"] is None
    assert replay["verified"] and replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["receipt_sha256"] == sha(stage / "SUMMARY.json")
    assert replay["bindings_sha256"] == sha(bindingspath)
    assert terminal["independent_process_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    assert [row["group"] for row in receipt["outcomes"]] == list(range(381))
    paid, associated = {}, 0
    for group, outcome in zip(data["groups"], receipt["outcomes"], strict=True):
        assert outcome["status"] in ("excluded", "pending")
        if outcome["status"] == "pending":
            continue
        path = stage / f"group-{group['id']:07}.json.gz"
        assert sha(path) == outcome["tree_sha256"]
        with gzip.open(path, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
            23, 14, group["centers"], group["faces"])
        assert tree["groups_sha256"] == digest and tree["constants_sha256"] == constantshash
        assert tree["radius_upper"] == constants["radius_upper"]
        result = exact.verify(14, group["centers"], group["faces"], tree["nodes"], constants)
        assert result["verified"] and result["nodes"] == outcome["nodes"] and result["counts"] == outcome["counts"]
        assert F(result["minimum_force_margin"]) > 0
        assert outcome["members"] == group["members"]
        paid[group["id"]] = sha(path)
        associated += group["members"]
        frozen[str(path)] = sha(path)
    assert len(paid) == receipt["excluded_groups"] == replay["exact_groups_replayed"] == 21
    assert associated == receipt["catalog_members_excluded"] == replay["associated_member_count"]
    pendingpath = originpath.parent.parent / "PENDING.jsonl"
    assert sha(pendingpath) == accepted["pending_sha256"]
    for path, expectedhash in receipt["frozen_files"].items():
        assert sha(path) == expectedhash
        frozen[path] = expectedhash
    for path in (Path(__file__), sourcepath, originpath, groupspath, bindingspath, pendingpath,
                 stage / "SUMMARY.json", stage / "EXACT-REPLAY.json", stage / "REPLAY-TERMINAL.json",
                 controlpath, constantspath, HIGH / "audit_streamed_hierarchy.py", HIGH / "exact_graph.py"):
        frozen[str(path)] = sha(path)
    for path, value in frozen.items():
        assert sha(path) == value
    output.mkdir()
    catalog = BinaryRows(catalogpath)
    with pendingpath.open(encoding="ascii") as origin, \
            bindingspath.open(encoding="ascii") as bindings, \
            (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        counts = scan(catalog.rows(), origin, bindings, data["groups"], paid, sha(catalogpath),
                      8277632, 2551670, ledger, residual)
    assert catalog.finished and counts["old-origin-obstruction"] == 5725962
    assert counts["new-strict-pair-type"] == associated
    for path, value in frozen.items():
        assert sha(path) == value
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-original-origin-and-fresh-pair-disjoint-payment-v1",
        "N": 23, "B": 14, "original_catalog_types": 8277632,
        "previous_pending_full_types": 2551670, "counts": counts,
        "additional_strict_pair_types": associated, "pending_full_types": counts["pending"],
        "all_source_indices_original_origin_status_and_actual_pair_maps_independently_scanned": True,
        "all_21_positive_pair_trees_freshly_exact_replayed_again": True,
        "old_origin_payments_not_recounted_as_new_strict_types": True,
        "parent_origin_report_sha256": sha(originpath),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "complete_source_induction_actual_cover_interface_and_other_families_still_upstream": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 whole original-source pair payment independently accepted:", counts, flush=True)


if __name__ == "__main__":
    main()
