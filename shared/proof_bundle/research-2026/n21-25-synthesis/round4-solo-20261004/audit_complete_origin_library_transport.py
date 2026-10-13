"""Fresh full-parent weak-force replay plus exact whole-outer library transport.

Library matches are conditional SAME-ORDER filling-family theorems, not weak
subgraph geometry exclusions. Every old positive tree is independently replayed
and every new match requires exact equality of the entire outer face image.
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
from n25_outer_search import read, publish
from batch_origin_collar import parent_gate, catalog_rows
from linked_filling_library import library_gate, make_index, lookup_exact_outer
from audit_complete_origin_finer_supplement import valid_payment_partition
import exact_graph as exact

assert __debug__


def pending_source(row, unresolved, original):
    assert type(unresolved["parent_index"]) is int
    assert unresolved["parent_index"] == original["parent_index"] == row["id"]
    assert (unresolved["centers"], unresolved["faces"]) == (
        original["centers"], original["faces"]) == (row["centers"], row["faces"])
    assert unresolved["not_a_geometric_exclusion"] is True
    assert (unresolved["batch"], unresolved["group"]) == (
        original["source_batch"], original["source_local_group"])


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "library", "transport-controls", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    snapshotpath, librarypath, transportpath, controlpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("snapshot", "library", "transport-controls", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (
        snapshotpath, librarypath, transportpath, controlpath, output))
    assert not output.exists()
    libraryhash = sha(librarypath)
    controls, transport = read(controlpath), read(transportpath)
    assert controls["verified"] and controls["schema"] == "complete-origin-library-parent-merge-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_complete_origin_library_transport.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert transport["verified"] and transport["schema"] == "strict-linked-family-exact-outer-transport-controls-v1"
    assert transport["source_sha256"] == sha(ROOT / "test_linked_filling_library.py")
    assert transport["library_sha256"] == libraryhash
    assert transport["known_exact_N25_attaining_outer_graph_not_strictly_matched"]
    assert transport["all_library_branch_trees_fresh_exact_replayed"]
    snapshot = read(snapshotpath)
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert snapshot["all_full_parent_pending_rows_frozen_once"]
    files = dict(snapshot["frozen_files"])
    for path, digest in files.items():
        assert sha(path) == digest
    parent = {name: Path(value) for name, value in snapshot["parent_inputs"].items()}
    basepath = parent["payments"]
    base = read(basepath / "VERIFIED.json")
    assert base["verified"] and base["schema"] == "complete-streamed-collar-batch-payment-audit-v1"
    assert base["source_sha256"] == sha(ROOT / "audit_origin_collar_batches.py")
    assert base["all_parent_rows_stream_compared_against_exact_batch_inputs"]
    assert base["all_excluded_trees_fresh_exact_replayed_again"]
    assert sha(basepath / "PAYMENTS.jsonl") == base["payments_sha256"]
    assert sha(basepath / "PENDING.jsonl") == base["pending_sha256"]
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    N, B, total = union["N"], union["B"], union["unique_necessary_weak_graphs"]
    assert N == 25 and B == 16
    assert (base["N"], base["B"], base["parent_weak_graphs"]) == (N, B, total)
    assert total == snapshot["parent_weak_graphs"]
    assert base["parent_catalog_sha256"] == sha(catalogpath)
    assert base["pending_weak_graphs"] == snapshot["selected_pending_graphs"] == len(snapshot["graphs"])
    original = {row["parent_index"]: row for row in snapshot["graphs"]}
    assert len(original) == len(snapshot["graphs"])
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    assert constants["verified"] and constants["N"] == N
    library, libraryfiles = library_gate(librarypath)
    assert library["pattern_count"] == transport["source_patterns"]
    files.update(libraryfiles)
    index = make_index(library)
    batch_size = read(parent["partition"])["batch_size"]
    output.mkdir()
    counts = Counter()
    with (basepath / "PAYMENTS.jsonl").open(encoding="ascii") as oldpaid, \
            (basepath / "PENDING.jsonl").open(encoding="ascii") as oldpending, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual, \
            (output / "EXACT-OUTER-TRANSPORTS.jsonl").open("x", encoding="ascii") as transports:
        partition = valid_payment_partition(total, oldpaid, oldpending)
        for row in catalog_rows(catalogpath, N, B, total):
            parent_id, payment, unresolved = next(partition)
            assert parent_id == row["id"]
            if payment is not None:
                assert parent_id not in original
                assert payment["status"] == "strict-exact-weak-graph-exclusion"
                batch, local = divmod(parent_id, batch_size)
                assert (payment["batch"], payment["group"]) == (batch, local)
                groupspath = parent["partition"].parent / f"batch-{batch:06}/GROUPS.json"
                treepath = groupspath.parent / f"PROPOSALS/group-{local:07}.json.gz"
                assert sha(treepath) == payment["tree_sha256"]
                with gzip.open(treepath, "rt", encoding="utf8") as stream:
                    tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
                assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                    N, B, row["centers"], row["faces"])
                if str(groupspath) not in files:
                    files[str(groupspath)] = sha(groupspath)
                assert tree["groups_sha256"] == files[str(groupspath)]
                assert tree["constants_sha256"] == constantshash
                assert tree["radius_upper"] == constants["radius_upper"]
                result = exact.verify(B, row["centers"], row["faces"], tree["nodes"], constants)
                assert result["verified"] and F(result["minimum_force_margin"]) > 0
                assert str(F(result["minimum_force_margin"])) == payment["minimum_force_margin"]
                files[str(treepath)] = payment["tree_sha256"]
                files[str(groupspath)] = tree["groups_sha256"]
                counts["old-strict-weak-force"] += 1
            else:
                assert parent_id in original
                pending_source(row, unresolved, original[parent_id])
                match = lookup_exact_outer(index, N, B, row["centers"], row["faces"])
                if match is None:
                    counts["pending"] += 1
                    residual.write(json.dumps(unresolved, separators=(",", ":"))+"\n")
                else:
                    pattern, mapping, checked = match
                    assert checked["exact_complete_outer_face_image_equal"]
                    assert checked["requires_complete_same_order_simple_disk_completion"]
                    transports.write(json.dumps({
                        "parent_index": parent_id, "pattern": pattern["id"],
                        "map": mapping, "fresh_exact_transport": checked,
                    }, separators=(",", ":"))+"\n")
                    payment = {
                        "parent_index": parent_id, "status": "strict-complete-filling-family-exact-transport",
                        "pattern": pattern["id"], "proof_sha256": pattern["proof_sha256"],
                        "library_sha256": libraryhash,
                        "not_a_standalone_geometric_weak_graph_exclusion": True,
                    }
                    counts["new-strict-exact-outer-family-transport"] += 1
            if payment is not None:
                ledger.write(json.dumps(payment, separators=(",", ":"))+"\n")
            if (parent_id+1) % 5000 == 0:
                print("B16 complete-parent force/library reacceptance", parent_id+1, "/", total,
                      dict(counts), flush=True)
        assert next(partition, None) is None
    assert counts["old-strict-weak-force"] == base["strictly_excluded"]
    assert counts["new-strict-exact-outer-family-transport"]+counts["pending"] == base["pending_weak_graphs"]
    assert sum(counts.values()) == total
    for path in (Path(__file__), snapshotpath, librarypath, transportpath, controlpath,
                 basepath / "VERIFIED.json", basepath / "PAYMENTS.jsonl", basepath / "PENDING.jsonl",
                 constants_path, HIGH / "exact_graph.py", Path(exact.kernel.__file__),
                 ROOT / "audit_complete_origin_finer_supplement.py"):
        files[str(path.resolve())] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-origin-parent-exact-outer-library-transport-merge-v1",
        "N": N, "B": B, "complete_parent_weak_graphs": total, "counts": dict(counts),
        "remaining_weak_graphs": counts["pending"],
        "all_residual_weak_lower_bounds_paid": counts["pending"] == 0,
        "all_parent_indices_disjointly_partitioned_once": True,
        "every_old_positive_weak_tree_freshly_mathematically_replayed": True,
        "all_library_complete_filling_trees_freshly_mathematically_replayed": True,
        "every_new_transport_requires_exact_complete_outer_face_equality": True,
        "new_library_payments_target_only_old_exact_pending_parent_indices": True,
        "payments_sha256": sha(output / "PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"),
        "transports_sha256": sha(output / "EXACT-OUTER-TRANSPORTS.jsonl"),
        "base_report_sha256": sha(basepath / "VERIFIED.json"),
        "library_sha256": libraryhash, "frozen_files": files,
        "source_sha256": sha(Path(__file__)),
        "conditional_completions_not_standalone_weak_subgraph_geometry": True,
        "source_cover_transport_other_boundary_families_and_exact_upper_still_required": True,
        "global_optimality_proved": False,
    })
    print("B16 full-parent exact library transport independently accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
