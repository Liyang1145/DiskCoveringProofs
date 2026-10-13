"""Group only the actual accepted N23/B14 binary-source origin residual."""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from paid_binary_residual import BinaryRows
from group_catalog import canonical
from audit_streamed_hierarchy import check_map
from partition_n23_B14_binary_origin import independent_mask, header, source_gate
from n25_outer_search import read, publish

assert __debug__


def group_selected(rows, pending, digest, total, expected, destination):
    assert json.loads(next(pending), object_pairs_hook=no_duplicate_keys) == header(
        "not-paid-by-origin-condition", digest)
    previous = -1

    def advance():
        nonlocal previous
        line = pending.readline()
        if not line:
            return None
        row = json.loads(line, object_pairs_hook=no_duplicate_keys)
        assert set(row) == {"index", "exposed_mask"}
        assert type(row["index"]) is int and previous < row["index"] < total
        assert type(row["exposed_mask"]) is int
        previous = row["index"]
        return row

    selected = advance()
    groups, counts = {}, Counter()
    sourcecount = selectedcount = 0
    started = time.monotonic()
    for index, row in rows:
        assert index == sourcecount
        sourcecount += 1
        assert len(row["faces"]) == 30
        mask = independent_mask(row["faces"])
        assert selected is None or selected["index"] >= index
        if mask == (1 << 23)-1:
            assert selected is None or selected["index"] != index
        else:
            assert selected is not None and selected == {"index": index, "exposed_mask": mask}
            code, mapping = canonical(23, 14, row["faces"], 2)
            gid = groups.setdefault(code, len(groups))
            group = {"id": gid, "centers": len(mapping["centers"]), "faces": list(code)}
            check_map(23, 14, group, mapping, set(row["faces"]), 2)
            counts[gid] += 1
            selectedcount += 1
            destination.write(json.dumps({
                "index": index, "group": gid, "map": mapping,
            }, separators=(",", ":"))+"\n")
            selected = advance()
        if sourcecount % 100000 == 0:
            destination.flush()
            print("N23/B14 actual residual grouped source", sourcecount, "/", total,
                  "selected", selectedcount, "groups", len(groups), "seconds",
                  round(time.monotonic()-started, 1), flush=True)
    assert sourcecount == total and selected is None
    assert selectedcount == expected and sum(counts.values()) == expected
    ordered = [None]*len(groups)
    for code, gid in groups.items():
        centers = max(mask.bit_length() for mask in code)
        ordered[gid] = {"id": gid, "centers": centers,
                        "faces": list(code), "members": counts[gid]}
    return ordered, selectedcount


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "partition", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    sourcepath, partitionpath, controlpath, output = (
        getattr(args, name).resolve() for name in ("source", "partition", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (sourcepath, partitionpath, controlpath, output))
    assert not output.exists()
    catalogpath, frozen = source_gate(sourcepath)
    accepted, controls = read(partitionpath), read(controlpath)
    assert accepted["verified"]
    assert accepted["schema"] == "independent-complete-original-N23-B14-origin-partition-v1"
    assert accepted["source_sha256"] == sha(ROOT / "partition_n23_B14_binary_origin.py")
    assert (accepted["N"], accepted["B"], accepted["source_types"]) == (23, 14, 8277632)
    assert accepted["pending_types"] == 2551670
    assert accepted["catalog_sha256"] == sha(catalogpath)
    assert accepted["source_report_sha256"] == sha(sourcepath)
    assert controls["verified"]
    assert controls["schema"] == "N23-B14-original-origin-residual-group-selection-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_B14_residual_grouping.py")
    assert controls["group_source_sha256"] == sha(Path(__file__))
    pendingpath = partitionpath.parent.parent / "PENDING.jsonl"
    assert sha(pendingpath) == accepted["pending_sha256"]
    for path in (Path(__file__), sourcepath, partitionpath, pendingpath, controlpath,
                 HIGH / "group_catalog.py", HIGH / "audit_streamed_hierarchy.py",
                 HIGH / "paid_binary_residual.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 23, "B": 14, "catalog_sha256": sha(catalogpath),
        "origin_partition_report_sha256": sha(partitionpath),
        "actual_origin_residual_types": 2551670, "threshold": 2,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "new_type_lower_bound_payments_not_claimed": True,
        "global_optimality_proved": False,
    })
    bindingpath = output / "bindings.jsonl"
    catalog = BinaryRows(catalogpath)
    with pendingpath.open(encoding="ascii") as pending, \
            bindingpath.open("x", encoding="ascii") as destination:
        groups, count = group_selected(catalog.rows(), pending, sha(catalogpath),
                                       8277632, 2551670, destination)
    assert catalog.finished
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "GROUPS.json", {
        "N": 23, "B": 14, "threshold": 2,
        "group_count": len(groups), "groups": groups,
        "selected_types": count, "catalog_types": 8277632,
        "catalog_sha256": sha(catalogpath), "bindings_file": bindingpath.name,
        "bindings_sha256": sha(bindingpath),
        "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": True,
        "selection_is_not_yet_an_accepted_exclusion": True,
        "parent_groups_sha256": None,
        "parent_proof_sha256": sha(partitionpath),
        "selection_kind": "actual-complete-origin-residual-not-whole-catalog",
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    publish(output / "RESTORED-SELECTION.json", {
        "schema": "N23-B14-origin-residual-source-and-exposed-group-restoration-v1",
        "N": 23, "B": 14, "all_source_types_scanned": 8277632,
        "actual_selected_residual_types": count, "exposed_pair_groups": len(groups),
        "every_selected_original_face_center_anchor_map_checked": True,
        "all_original_origin_obstructions_skipped_without_recounting": True,
        "groups_sha256": sha(output / "GROUPS.json"),
        "bindings_sha256": sha(bindingpath), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "independent_selection_map_audit_and_all_new_force_replays_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 actual original residual grouped:", count, len(groups),
          "; no new lower-bound payment", flush=True)


if __name__ == "__main__":
    main()
