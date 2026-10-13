"""Stream exact batch replays against every parent row; never pay pending rows."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from batch_origin_collar import parent_gate, catalog_rows, identity

assert __debug__


def verify_tree(N, B, group, outcome, receiptpath, digest, constants, constantshash):
    treepath = receiptpath.parent / f"group-{group['id']:07}.json.gz"
    assert sha(treepath) == outcome["tree_sha256"]
    with gzip.open(treepath, "rt", encoding="utf8") as stream:
        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
    assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
        N, B, group["centers"], group["faces"]), "tree/batch graph mismatch"
    assert tree["groups_sha256"] == digest and tree["constants_sha256"] == constantshash
    assert tree["radius_upper"] == constants["radius_upper"], "tree radius threshold mismatch"
    result = exact.verify(B, group["centers"], group["faces"], tree["nodes"], constants)
    assert result["verified"] and result["nodes"] == outcome["nodes"]
    assert result["counts"] == outcome["counts"] and outcome["members"] == 1
    assert sha(treepath) == outcome["tree_sha256"]
    margin = F(result["minimum_force_margin"])
    assert margin > 0
    return result, margin


def audit(manifestpath, terminalpath, unionpath, partitionpath, output):
    assert not output.exists()
    union, catalogpath, parentbindings = parent_gate(manifestpath, terminalpath, unionpath)
    report = read(partitionpath)
    N, B, total = union["N"], union["B"], union["unique_necessary_weak_graphs"]
    assert report["verified"] and report["schema"] == "complete-collar-union-bounded-partition-v1"
    assert (report["N"], report["B"], report["weak_graph_count"]) == (N, B, total)
    assert report["source_sha256"] == sha(ROOT / "batch_origin_collar.py")
    assert report["all_parent_rows_canonical_checked"] and report["all_parent_identity_bindings_checked"]
    assert report["complete_parent_union_partitioned_once"]
    assert report["manifest_sha256"] == sha(manifestpath)
    assert report["native_terminal_sha256"] == sha(terminalpath)
    assert report["parent_union_report_sha256"] == sha(unionpath)
    assert report["parent_catalog_sha256"] == sha(catalogpath)
    assert report["parent_bindings_sha256"] == sha(parentbindings)
    descriptorpath = partitionpath.parent / report["descriptor_file"]
    assert descriptorpath.parent == partitionpath.parent and sha(descriptorpath) == report["descriptor_sha256"]
    constantspath = HIGH.parent / f"evidence/core-reduction/constants/n{N}.json"
    constants = read(constantspath)
    assert constants["N"] == N and constants["verified"]
    constantshash = sha(constantspath)
    cataloghash, unionhash = sha(catalogpath), sha(unionpath)
    output.mkdir()
    payments, pendingpath = output / "PAYMENTS.jsonl", output / "PENDING.jsonl"
    stagepath = output / "AUDITED-STAGES.jsonl"
    count = paid = pending = batches = 0
    minimum = None
    parent_rows = iter(catalog_rows(catalogpath, N, B, total))
    with descriptorpath.open(encoding="ascii") as descriptors, payments.open("x", encoding="ascii") as ledger, \
            pendingpath.open("x", encoding="ascii") as unresolved, stagepath.open("x", encoding="ascii") as stages:
        for line in descriptors:
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert descriptor["batch"] == batches and descriptor["first"] == count, "batch index/range gap or duplication"
            groupspath = (partitionpath.parent / descriptor["groups_file"]).resolve()
            assert groupspath == (partitionpath.parent / f"batch-{batches:06}/GROUPS.json").resolve()
            assert sha(groupspath) == descriptor["groups_sha256"]
            groups = read(groupspath)
            assert (groups["N"], groups["B"], groups["group_count"]) == (N, B, descriptor["count"])
            assert groups["selected_types"] == descriptor["count"] and groups["catalog_types"] == total
            assert groups["parent_catalog_first_index"] == count and groups["batch_number"] == batches
            assert groups["catalog_sha256"] == cataloghash
            assert groups["parent_union_report_sha256"] == unionhash
            assert groups["members_are_necessary_weak_graphs_not_full_types"]
            bindingpath = groupspath.parent / groups["bindings_file"]
            assert bindingpath == groupspath.parent / "bindings.jsonl"
            assert sha(bindingpath) == descriptor["bindings_sha256"] == groups["bindings_sha256"]
            receiptpath, replaypath = groupspath.parent / "PROPOSALS/SUMMARY.json", groupspath.parent / "EXACT-REPLAY.json"
            receipt, replay = map(read, (receiptpath, replaypath))
            receipthash, replayhash = sha(receiptpath), sha(replaypath)
            digest = sha(groupspath)
            assert receipt["groups_sha256"] == replay["groups_sha256"] == digest
            assert (receipt["N"], receipt["B"]) == (replay["N"], replay["B"]) == (N, B)
            assert receipt["requested_groups_complete"]
            assert receipt["source_sha256"] == sha(ROOT / "probe_collar_batches.py")
            assert replay["verified"] and replay["receipt_sha256"] == sha(receiptpath)
            assert replay["bindings_sha256"] == sha(bindingpath)
            assert replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
            assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
            outcomes = {r["group"]: r for r in receipt["outcomes"]}
            assert len(outcomes) == len(receipt["outcomes"]) == groups["group_count"]
            assert set(outcomes) == set(range(groups["group_count"]))
            batch_paid = 0
            with bindingpath.open(encoding="ascii") as bindings:
                for local, group in enumerate(groups["groups"]):
                    assert group["id"] == local and group["members"] == 1
                    parent = next(parent_rows)
                    assert parent["id"] == count
                    assert (group["centers"], group["faces"]) == (parent["centers"], parent["faces"]), "parent/batch weak graph mismatch"
                    binding = json.loads(next(bindings), object_pairs_hook=no_duplicate_keys)
                    assert binding == {"index": count, "group": local, "map": identity(group["centers"], B)}, "batch identity binding mismatch"
                    outcome = outcomes[local]
                    assert outcome["status"] in ("excluded", "pending")
                    if outcome["status"] == "pending":
                        unresolved.write(json.dumps({"parent_index": count, "batch": batches, "group": local,
                                                      "centers": group["centers"], "faces": group["faces"],
                                                      "not_a_geometric_exclusion": True},
                                                     separators=(",", ":"))+"\n")
                        pending += 1
                    else:
                        result, margin = verify_tree(N, B, group, outcome, receiptpath,
                                                     digest, constants, constantshash)
                        minimum = margin if minimum is None else min(minimum, margin)
                        ledger.write(json.dumps({"parent_index": count, "batch": batches, "group": local,
                                                 "status": "strict-exact-weak-graph-exclusion",
                                                 "tree_sha256": outcome["tree_sha256"],
                                                 "minimum_force_margin": str(margin)},
                                                separators=(",", ":"))+"\n")
                        paid += 1
                        batch_paid += 1
                    count += 1
                assert not bindings.read().strip()
            assert batch_paid == receipt["excluded_groups"] == replay["exact_groups_replayed"]
            assert groups["group_count"]-batch_paid == receipt["pending_groups"] == replay["pending_groups"]
            assert batch_paid == receipt["catalog_members_excluded"] == replay["associated_member_count"]
            assert sha(groupspath) == descriptor["groups_sha256"]
            assert sha(receiptpath) == receipthash and sha(replaypath) == replayhash
            stages.write(json.dumps({"batch": batches, "groups_sha256": digest,
                                     "receipt_sha256": receipthash, "replay_sha256": replayhash,
                                     "bindings_sha256": sha(bindingpath), "paid": batch_paid,
                                     "pending": groups["group_count"]-batch_paid},
                                    separators=(",", ":"))+"\n")
            batches += 1
    assert next(parent_rows, None) is None
    assert count == total == paid+pending and batches == report["batch_count"]
    assert sha(descriptorpath) == report["descriptor_sha256"] and sha(constantspath) == constantshash
    parent_gate(manifestpath, terminalpath, unionpath)
    assert sha(catalogpath) == cataloghash and sha(unionpath) == unionhash
    result = {
        "verified": True, "schema": "complete-streamed-collar-batch-payment-audit-v1", "N": N, "B": B,
        "all_parent_rows_stream_compared_against_exact_batch_inputs": True,
        "all_excluded_trees_fresh_exact_replayed_again": True,
        "parent_weak_graphs": total, "strictly_excluded": paid, "pending_weak_graphs": pending,
        "all_residual_weak_lower_bounds_paid": pending == 0, "batch_count": batches,
        "minimum_force_margin": None if minimum is None else str(minimum),
        "parent_union_report_sha256": sha(unionpath), "parent_catalog_sha256": sha(catalogpath),
        "partition_report_sha256": sha(partitionpath), "descriptor_sha256": sha(descriptorpath),
        "payments_sha256": sha(payments), "pending_sha256": sha(pendingpath),
        "audited_stages_sha256": sha(stagepath),
        "constants_sha256": constantshash, "source_sha256": sha(Path(__file__)),
        "exact_checker_sha256": sha(HIGH / "exact_graph.py"),
        "parent_requires_actual_cover_origin_condition": True,
        "not_an_unqualified_geometric_weak_graph_family": True,
        "source_cover_transport_and_other_families_still_required": True,
        "global_optimality_proved": False,
    }
    publish(output / "VERIFIED.json", result)
    return result


def main():
    ap = argparse.ArgumentParser()
    for name in ("manifest", "terminal", "union", "partition", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    result = audit(*(getattr(args, name).resolve()
                     for name in ("manifest", "terminal", "union", "partition", "output")))
    print("Complete parent-to-batch exact payment audit accepted:",
          result["strictly_excluded"], "strict,", result["pending_weak_graphs"], "pending", flush=True)


if __name__ == "__main__":
    main()
