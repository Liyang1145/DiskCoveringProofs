"""Independent strict increment on every actual previous unpaid full source type.

Previously accepted source/old-tree proofs are bound prerequisites, not
claimed freshly mathematically replayed here. Indexed original source rows
and full exposed maps are checked again for ALL current pending types.
"""
from pathlib import Path
from collections import Counter
import argparse
import gzip
import json
import struct
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from paid_binary_residual import BinaryRows
from audit_streamed_hierarchy import check_map
from audit_n23_B15_effective_outer_payment import pending_indices
from audit_n23_B14_full_outer_payment import check_tree, independent_mask
from n25_outer_search import read, publish

assert __debug__


def decode_record(block, N, B):
    length = 2*N-B-2
    assert len(block) == 4*(length+1)
    stabilizer, *faces = struct.unpack("<"+"I"*(length+1), block)
    assert type(stabilizer) is int and stabilizer > 0 and 2*B % stabilizer == 0
    assert len(faces) == length and faces == sorted(set(faces))
    assert all(0 < mask < 1 << N and mask.bit_count() == 3 for mask in faces)
    return {"stabilizer": stabilizer, "faces": faces}


class IndexedOriginal:
    def __init__(self, path):
        self.catalog = BinaryRows(path)
        self.header = self.catalog.header
        assert (self.header["N"], self.header["B"], self.header["orbits"]) == (23, 14, 8277632)
        assert self.header["proof_prunes"] == 0 and self.header["proof_payments"] == []
        self.offset = self.catalog.stream.tell()
        self.recordsize = 4*(self.catalog.F+1)
        assert Path(path).stat().st_size == self.offset+self.recordsize*self.header["orbits"]

    def at(self, index):
        assert type(index) is int and 0 <= index < self.header["orbits"]
        self.catalog.stream.seek(self.offset+index*self.recordsize)
        block = self.catalog.stream.read(self.recordsize)
        return decode_record(block, 23, 14)

    def close(self):
        self.catalog.stream.close()


def selected_groups(data, receipt):
    assert (data["N"], data["B"], data["threshold"]) == (23, 14, 1)
    assert (receipt["N"], receipt["B"]) == (23, 14)
    assert receipt["requested_groups_complete"]
    groups, outcomes = data["groups"], receipt["outcomes"]
    assert [group["id"] for group in groups] == list(range(data["group_count"]))
    assert [row["group"] for row in outcomes] == list(range(data["group_count"]))
    assert all(row["status"] in ("excluded", "pending") for row in outcomes)
    paid = {row["group"] for row in outcomes if row["status"] == "excluded"}
    pending = [row["group"] for row in outcomes if row["status"] == "pending"]
    assert len(paid) == receipt["excluded_groups"] and len(pending) == receipt["pending_groups"]
    assert sum(groups[gid]["members"] for gid in paid) == receipt["catalog_members_excluded"]
    assert sum(group["members"] for group in groups) == data["selected_types"]
    return pending, paid


def adopt(pending, bindings, at, groups, oldpaid, newpaid, total, expected, ledger, residual):
    current = next(pending, None)
    previous = -1
    membercounts, counts = Counter(), Counter()
    assert [group["id"] for group in groups] == list(range(len(groups)))
    assert set(newpaid).issubset(set(range(len(groups)))-oldpaid)
    for line in bindings:
        binding = json.loads(line, object_pairs_hook=no_duplicate_keys)
        index, gid = binding["index"], binding["group"]
        assert type(index) is int and previous < index < total
        assert type(gid) is int and 0 <= gid < len(groups)
        assert current is None or type(current) is int and current >= index
        previous = index
        membercounts[gid] += 1
        if gid in oldpaid:
            assert current != index, "previous paid type reintroduced in current residual"
            continue
        assert current == index, "actual pending group member absent from accepted current residual"
        row = at(index)
        assert len(row["faces"]) == 30
        mask = independent_mask(row["faces"])
        assert groups[gid]["centers"] == mask.bit_count() < 23
        check_map(23, 14, groups[gid], binding["map"], set(row["faces"]), 1)
        if gid in newpaid:
            counts["new-strict-full-outer-type"] += 1
            ledger.write(json.dumps({
                "index": index, "group": gid, "tree_sha256": newpaid[gid],
            }, separators=(",", ":"))+"\n")
        else:
            counts["pending"] += 1
            residual.write(json.dumps({"index": index}, separators=(",", ":"))+"\n")
        current = next(pending, None)
    assert current is None
    assert all(membercounts[group["id"]] == group["members"] > 0 for group in groups)
    assert sum(counts.values()) == expected
    return dict(counts)


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "parent", "groups", "previous-stage", "stage", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    sourcepath, parent, groupspath, previous, stage, controlpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("source", "parent", "groups", "previous-stage", "stage", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (
        sourcepath, parent, groupspath, previous, stage, controlpath, output))
    assert not output.exists()
    accepted, data, old, receipt, controls, source = map(read, (
        parent / "VERIFIED.json", groupspath, previous / "SUMMARY.json",
        stage / "SUMMARY.json", controlpath, sourcepath))
    assert accepted["verified"]
    assert accepted["schema"] == "N23-B14-current-residual-full-outer-disjoint-payment-v1"
    assert accepted["source_sha256"] == sha(ROOT / "audit_n23_B14_full_outer_payment.py")
    assert (accepted["N"], accepted["B"], accepted["original_catalog_types"]) == (23, 14, 8277632)
    assert accepted["all_source_rows_previous_payment_partition_and_current_full_outer_maps_checked"]
    assert accepted["all_new_positive_full_outer_trees_freshly_exact_replayed_again"]
    assert accepted["previous_paid_types_not_reintroduced_or_recounted_as_new"]
    frozen = dict(accepted["frozen_files"])
    for path in (sourcepath, groupspath, previous / "SUMMARY.json"):
        assert frozen[str(path)] == sha(path)
    assert source["verified"] and source["source_sha256"] == sha(ROOT / "accept_n23_B14_restored_source.py")
    assert source["schema"] == "restored-N23-B14-historical-complete-source-and-fresh-union-gates-v1"
    catalogpath = (ROOT / source["catalog_relative_to_round4"]).resolve()
    assert catalogpath.is_relative_to(ROOT) and sha(catalogpath) == source["catalog_sha256"]
    assert frozen[str(catalogpath)] == sha(catalogpath)
    groupshash = sha(groupspath)
    assert old["groups_sha256"] == groupshash
    assert old["source_sha256"] == sha(ROOT / "propose_isolated_small_order_groups.py")
    assert old["known_attaining_group_control"] is None
    expected_ids, oldpaid = selected_groups(data, old)
    expected = sum(data["groups"][gid]["members"] for gid in expected_ids)
    assert expected == accepted["pending_full_types"] > 0
    assert len(oldpaid) == accepted["positive_groups"]
    assert receipt["source_sha256"] == sha(ROOT / "propose_n23_B14_pending_outer.py")
    assert receipt["groups_sha256"] == groupshash
    assert receipt["parent_report_sha256"] == sha(parent / "VERIFIED.json")
    assert receipt["previous_stage_receipt_sha256"] == sha(previous / "SUMMARY.json")
    assert receipt["requested_unpaid_groups_complete"]
    assert receipt["selected_unpaid_group_ids"] == expected_ids
    assert (receipt["N"], receipt["B"]) == (23, 14)
    assert [row["group"] for row in receipt["outcomes"]] == expected_ids
    assert all(row["status"] in ("excluded", "pending") for row in receipt["outcomes"])
    assert controls["verified"]
    assert controls["schema"] == "N23-B14-current-pending-outer-increment-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_B14_pending_outer.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["proposal_source_sha256"] == sha(ROOT / "propose_n23_B14_pending_outer.py")
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    paid, associated = {}, 0
    for outcome in receipt["outcomes"]:
        if outcome["status"] == "pending":
            continue
        gid = outcome["group"]
        assert gid not in oldpaid
        treepath = stage / f"group-{gid:07}.json.gz"
        assert sha(treepath) == outcome["tree_sha256"]
        with gzip.open(treepath, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        check_tree(tree, data["groups"][gid], outcome, groupshash, constants, constantshash)
        paid[gid] = sha(treepath)
        associated += data["groups"][gid]["members"]
        frozen[str(treepath)] = sha(treepath)
    assert len(paid) == receipt["excluded_groups"]
    assert len(expected_ids)-len(paid) == receipt["pending_groups"]
    assert associated == receipt["catalog_members_excluded"]
    bindingspath = (groupspath.parent / data["bindings_file"]).resolve()
    pendingpath = parent / "PENDING.jsonl"
    assert bindingspath.is_relative_to(ROOT) and sha(bindingspath) == data["bindings_sha256"]
    assert sha(pendingpath) == accepted["pending_sha256"]
    assert sha(parent / "ADDITIONAL-PAYMENTS.jsonl") == accepted["additional_payments_sha256"]
    for path, digest in receipt["frozen_files"].items():
        assert path not in frozen or frozen[path] == digest
        frozen[path] = digest
    for path in (Path(__file__), sourcepath, parent / "VERIFIED.json", pendingpath,
                 parent / "ADDITIONAL-PAYMENTS.jsonl", groupspath, bindingspath,
                 previous / "SUMMARY.json", stage / "SUMMARY.json", controlpath,
                 constantspath, ROOT / "audit_n23_B14_full_outer_payment.py",
                 HIGH / "audit_streamed_hierarchy.py", HIGH / "paid_binary_residual.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    catalog = IndexedOriginal(catalogpath)
    with bindingspath.open(encoding="ascii") as bindings, \
            (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        counts = adopt(pending_indices(pendingpath, 8277632), bindings, catalog.at,
                       data["groups"], oldpaid, paid, 8277632, expected, ledger, residual)
    catalog.close()
    assert counts.get("new-strict-full-outer-type", 0) == associated
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-current-pending-full-outer-strict-increment-v1",
        "N": 23, "B": 14, "original_catalog_types": 8277632,
        "previous_pending_full_types": expected, "counts": counts,
        "additional_strict_full_outer_types": associated, "new_positive_groups": len(paid),
        "pending_full_types": counts.get("pending", 0),
        "every_previous_pending_source_index_partitioned_exactly_once": True,
        "every_current_pending_actual_complete_source_row_and_full_exposed_map_checked": True,
        "every_new_positive_force_tree_freshly_mathematically_replayed": True,
        "previous_source_and_old_tree_theorems_reused_unchanged_without_fresh_old_replay_claim": True,
        "not_a_new_full_original_catalog_scan": True,
        "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "complete_source_induction_actual_cover_transport_and_other_global_obligations_still_owed": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 actual pending full-outer strict increment accepted:", counts, flush=True)


if __name__ == "__main__":
    main()
