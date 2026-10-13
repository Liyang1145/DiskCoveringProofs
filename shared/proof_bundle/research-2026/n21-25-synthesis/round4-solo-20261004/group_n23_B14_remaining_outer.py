"""Restore all exposed constraints on only the verified current B14 residual."""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from paid_binary_residual import BinaryRows
from group_catalog import canonical
from audit_streamed_hierarchy import check_map
from audit_n23_B15_effective_outer_payment import pending_indices
from partition_n23_B14_binary_origin import source_gate, independent_mask
from n25_outer_search import read, publish

assert __debug__


def group_remaining(rows, pending, total, expected, destination):
    target = next(pending, None)
    sourcecount = selected = 0
    codes, members = {}, Counter()
    started = time.monotonic()
    for index, row in rows:
        assert type(index) is int and index == sourcecount
        sourcecount += 1
        assert target is None or type(target) is int and target >= index
        if target == index:
            assert len(row["faces"]) == 30
            mask = independent_mask(row["faces"])
            assert mask != (1 << 23)-1
            code, mapping = canonical(23, 14, row["faces"], 1)
            gid = codes.setdefault(code, len(codes))
            group = {"id": gid, "centers": len(mapping["centers"]), "faces": list(code)}
            assert group["centers"] == mask.bit_count() < 23
            check_map(23, 14, group, mapping, set(row["faces"]), 1)
            destination.write(json.dumps({
                "index": index, "group": gid, "map": mapping,
            }, separators=(",", ":"))+"\n")
            members[gid] += 1
            selected += 1
            target = next(pending, None)
        if sourcecount % 100000 == 0:
            destination.flush()
            print("N23/B14 full-exposed residual grouping source", sourcecount, "/", total,
                  "selected", selected, "groups", len(codes), "seconds",
                  round(time.monotonic()-started, 1), flush=True)
    assert sourcecount == total and target is None
    assert selected == expected and sum(members.values()) == expected
    groups = [None]*len(codes)
    for code, gid in codes.items():
        groups[gid] = {"id": gid, "faces": list(code),
                       "centers": max(mask.bit_length() for mask in code), "members": members[gid]}
    return groups, selected


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "parent", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    sourcepath, parent, controlpath, output = (
        getattr(args, name).resolve() for name in ("source", "parent", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (sourcepath, parent, controlpath, output))
    assert not output.exists()
    accepted, controls = read(parent / "VERIFIED.json"), read(controlpath)
    assert accepted["verified"] and accepted["schema"] == "N23-B14-original-origin-and-fresh-pair-disjoint-payment-v1"
    assert accepted["source_sha256"] == sha(ROOT / "audit_n23_B14_pair_payment.py")
    assert (accepted["N"], accepted["B"], accepted["original_catalog_types"]) == (23, 14, 8277632)
    assert accepted["all_source_indices_original_origin_status_and_actual_pair_maps_independently_scanned"]
    assert accepted["all_21_positive_pair_trees_freshly_exact_replayed_again"]
    assert accepted["old_origin_payments_not_recounted_as_new_strict_types"]
    assert accepted["pending_full_types"] == 2368183
    assert controls["verified"] and controls["schema"] == "N23-B14-verified-residual-full-outer-selection-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_B14_remaining_outer.py")
    assert controls["group_source_sha256"] == sha(Path(__file__))
    catalogpath, sourcefiles = source_gate(sourcepath)
    frozen = dict(accepted["frozen_files"])
    for path, digest in sourcefiles.items():
        if path in frozen:
            assert frozen[path] == digest
        frozen[path] = digest
    pendingpath = parent / "PENDING.jsonl"
    assert sha(pendingpath) == accepted["pending_sha256"]
    for path in (Path(__file__), sourcepath, parent / "VERIFIED.json", pendingpath,
                 controlpath, HIGH / "group_catalog.py", HIGH / "audit_streamed_hierarchy.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 23, "B": 14, "actual_selected_residual_types": 2368183, "threshold": 1,
        "parent_payment_report_sha256": sha(parent / "VERIFIED.json"),
        "parent_pending_sha256": sha(pendingpath), "frozen_files": frozen,
        "old_pair_and_origin_payments_not_reintroduced": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    bindingpath = output / "bindings.jsonl"
    catalog = BinaryRows(catalogpath)
    with bindingpath.open("x", encoding="ascii") as destination:
        groups, selected = group_remaining(
            catalog.rows(), pending_indices(pendingpath, 8277632), 8277632, 2368183, destination)
    assert catalog.finished
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "GROUPS.json", {
        "N": 23, "B": 14, "threshold": 1, "group_count": len(groups), "groups": groups,
        "selected_types": selected, "catalog_types": 8277632,
        "catalog_sha256": sha(catalogpath), "bindings_file": bindingpath.name,
        "bindings_sha256": sha(bindingpath), "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": True, "selection_is_not_yet_an_accepted_exclusion": True,
        "parent_groups_sha256": None, "parent_proof_sha256": sha(parent / "VERIFIED.json"),
        "selection_kind": "actual-verified-current-source-residual-all-exposed-faces",
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    publish(output / "RESTORED-SELECTION.json", {
        "schema": "N23-B14-verified-residual-full-outer-restoration-v1",
        "N": 23, "B": 14, "all_original_source_rows_scanned": 8277632,
        "actual_selected_residual_types": selected, "full_outer_groups": len(groups),
        "all_actual_exposed_faces_preserved_not_only_pair_faces": True,
        "every_selected_face_center_and_anchor_map_checked": True,
        "previous_paid_source_types_not_reintroduced_or_recounted": True,
        "groups_sha256": sha(output / "GROUPS.json"), "bindings_sha256": sha(bindingpath),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "independent_source_payment_adoption_and_lower_bounds_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 true residual full outer constraints restored:", selected, len(groups),
          "; no new type payment", flush=True)


if __name__ == "__main__":
    main()
