"""Bind complete original N23 residual types, without any lower-bound payment."""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import Catalog, sha, no_duplicate_keys
from audit_streamed_hierarchy import check_map
from audit_n23_B15_effective_outer_payment import pending_indices
from n25_outer_search import read, publish

assert __debug__


def extract(rows, bindings, pair_pending, residual_indices, groups, total,
            expected_residual, destination, N=23, B=15):
    pair = next(pair_pending, None)
    pending = next(residual_indices, None)
    source_count = binding_count = selected_count = 0
    all_members, selected_members = Counter(), Counter()
    previous_binding = -1
    started = time.monotonic()
    for index, row in rows:
        assert type(index) is int and index == source_count
        source_count += 1
        assert pair is None or type(pair) is int and pair >= index
        assert pending is None or type(pending) is int and pending >= index
        binding = None
        if pair == index:
            line = bindings.readline()
            assert line, "missing original outer binding"
            binding = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert type(binding["index"]) is int
            assert binding["index"] == index > previous_binding
            previous_binding = index
            gid = binding["group"]
            assert type(gid) is int and 0 <= gid < len(groups)
            assert groups[gid]["id"] == gid
            all_members[gid] += 1
            binding_count += 1
            pair = next(pair_pending, None)
        if pending == index:
            assert binding is not None, "residual source absent from outer parent"
            faces = row["faces"]
            assert type(faces) is list and faces == sorted(set(faces))
            assert len(faces) == 2*N-B-2
            assert all(type(mask) is int and 0 < mask < 1 << N
                       and mask.bit_count() == 3 for mask in faces)
            assert type(row["stabilizer"]) is int and row["stabilizer"] > 0
            check_map(N, B, groups[gid], binding["map"], set(faces), 1)
            inner = [mask for mask in faces if not mask & ((1 << B)-1)]
            exposed = [mask for mask in faces if mask & ((1 << B)-1)]
            assert len(exposed) == len(groups[gid]["faces"])
            selected_count += 1
            selected_members[gid] += 1
            destination.write(json.dumps({
                "index": index, "outer_group": gid,
                "stabilizer": row["stabilizer"], "faces": faces,
                "original_outer_map": binding["map"],
                "pure_internal_faces": inner,
                "no_lower_bound_payment_by_extraction": True,
            }, separators=(",", ":"))+"\n")
            pending = next(residual_indices, None)
        if source_count % 500000 == 0:
            print("N23 full residual source restoration", source_count, "/", total,
                  "selected", selected_count, "seconds",
                  round(time.monotonic()-started, 1), flush=True)
    assert source_count == total and pair is pending is None
    assert not bindings.read(1), "extra original outer binding"
    assert selected_count == expected_residual
    assert all(all_members[group["id"]] == group["members"] for group in groups)
    return binding_count, selected_count, dict(selected_members)


def main():
    ap = argparse.ArgumentParser()
    for name in ("dataset", "parent", "pair-maps", "outer", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    dataset, parent, pairmaps, outer, controlpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("dataset", "parent", "pair-maps", "outer", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (
        dataset, parent, pairmaps, outer, controlpath, output))
    assert not output.exists()
    accepted, mappings, controls = map(
        read, (parent / "VERIFIED.json", pairmaps, controlpath))
    assert controls["verified"]
    assert controls["schema"] == "N23-actual-full-residual-extraction-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_actual_residual_extraction.py")
    assert controls["extractor_source_sha256"] == sha(Path(__file__))
    assert accepted["verified"] and (accepted["N"], accepted["B"]) == (23, 15)
    assert accepted["schema"] == "iterative-original-N23-B15-residual-outer-strict-payment-v1"
    assert accepted["source_sha256"] == sha(ROOT / "audit_n23_followup_outer_stage.py")
    assert accepted["all_source_indices_and_original_outer_bindings_scanned"]
    assert accepted["every_previous_unpaid_actual_face_center_anchor_map_freshly_checked"]
    assert accepted["only_previous_pending_source_types_paid_no_prior_payment_recount"]
    assert accepted["original_catalog_types"] == 16790546
    assert 0 < accepted["pending_full_types"] < 3976
    assert mappings["verified"] and (mappings["N"], mappings["B"]) == (23, 15)
    assert mappings["source_sha256"] == sha(HIGH / "audit_streamed_hierarchy.py")
    assert mappings["disjoint_hierarchy_partition_verified"]
    assert mappings["catalog_types"] == 16790546 and mappings["pending_types"] == 13603249
    frozen = dict(accepted["frozen_files"])
    for path, expected in frozen.items():
        assert sha(path) == expected
    catalogpath = dataset / "CATALOG/N23-B15-dfs.json"
    groupspath = outer / "OUTER/GROUPS.json"
    bindingspath = outer / "OUTER/bindings.jsonl"
    pairpendingpath = pairmaps.parent / mappings["pending_indices_file"]
    pendingpath = parent / "PENDING.jsonl"
    assert pairpendingpath.resolve().is_relative_to(ROOT)
    assert sha(catalogpath) == mappings["catalog_sha256"] == frozen[str(catalogpath)]
    assert sha(pairpendingpath) == mappings["pending_indices_sha256"] == frozen[str(pairpendingpath)]
    assert sha(pendingpath) == accepted["pending_sha256"]
    assert sha(groupspath) == frozen[str(groupspath)]
    assert sha(bindingspath) == frozen[str(bindingspath)]
    data = read(groupspath)
    assert (data["N"], data["B"], data["threshold"], data["group_count"]) == (23, 15, 1, 535262)
    assert [group["id"] for group in data["groups"]] == list(range(535262))
    assert data["selected_types"] == 13603249
    assert data["bindings_sha256"] == sha(bindingspath)
    for path in (Path(__file__), ROOT / "test_n23_actual_residual_extraction.py",
                 parent / "VERIFIED.json", pendingpath, pairmaps, controlpath,
                 groupspath, bindingspath, pairpendingpath, catalogpath,
                 HIGH / "stream_catalog.py", HIGH / "audit_streamed_hierarchy.py",
                 ROOT / "audit_n23_B15_effective_outer_payment.py"):
        frozen[str(path.resolve())] = sha(path)
    output.mkdir()
    catalog = Catalog(catalogpath)
    assert (catalog.header["N"], catalog.header["B"], catalog.header["orbits"]) == (23, 15, 16790546)
    fullpath = output / "FULL-TYPES.jsonl"
    with bindingspath.open(encoding="ascii") as bindings, \
            fullpath.open("x", encoding="ascii") as destination:
        binding_count, selected_count, members = extract(
            catalog.rows(), bindings, pending_indices(pairpendingpath, 16790546),
            pending_indices(pendingpath, 16790546), data["groups"], 16790546,
            accepted["pending_full_types"], destination)
    assert catalog.finished and binding_count == 13603249
    assert sum(members.values()) == accepted["pending_full_types"]
    for path, expected in frozen.items():
        assert sha(path) == expected
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "original-N23-B15-actual-complete-residual-types-restoration-v1",
        "N": 23, "B": 15, "catalog_types": 16790546,
        "original_outer_binding_rows": binding_count,
        "actual_full_residual_types": selected_count,
        "selected_original_outer_group_members": members,
        "all_original_source_rows_and_bindings_scanned_to_real_end": True,
        "every_selected_complete_face_set_and_original_center_anchor_map_checked": True,
        "all_29_faces_preserved_including_pure_internal_faces": True,
        "only_current_parent_pending_indices_selected": True,
        "full_types_file": fullpath.name, "full_types_sha256": sha(fullpath),
        "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "pending_sha256": sha(pendingpath), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "not_a_new_mathematical_lower_bound_or_payment": True,
        "global_optimality_proved": False,
    })
    print("N23 actual complete residual types restored:", selected_count, members,
          "; no new lower-bound payment", flush=True)


if __name__ == "__main__":
    main()
