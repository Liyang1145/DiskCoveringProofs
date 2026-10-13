"""Whole actual-source candidate fiber control; no parent adoption or strict core."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha
from n24_actual_core_transport import own_core_gate, find_embedding, COREPATH
from propose_small_order_filling import propose
from small_order_filling_kernel import replay_payload
from mix_n24_core_family import check_mixed

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    controlpath = ROOT / "n24-own-core-transport-controls-v1/VERIFIED.json"
    controls = read(controlpath)
    assert controls["verified"] and controls["actual_attaining_outer_exactly_present_in_complete_original_source"]
    parent = controls["actual_entire_necessary_source_attaining_parent"]
    collar = {"N": 24, "B": 15, "centers": parent["centers"], "faces": parent["faces"]}
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n24.json")
    old = propose(collar, constants, 10000, 31, force_enabled=True)
    old["constants_sha256"] = sha(ROOT.parent / "evidence/core-reduction/constants/n24.json")
    old["source_collar_sha256"] = "CONTROL_ACTUAL_SOURCE_PARENT_IDENTITY_NOT_PRODUCTION_PAYMENT"
    old["kernel_sha256"] = sha(ROOT / "small_order_filling_kernel.py")
    old["source_sha256"] = "CONTROL_ACTUAL_SOURCE_CANDIDATE_STRICT_BRANCH_PROPOSAL"
    oldpaid = replay_payload(old, constants)
    assert oldpaid["pending_complete_leaves"] > 0 and oldpaid["unsearched_frontier_nodes"] == 0
    assert not oldpaid["whole_completion_family_strictly_closed"]
    proof = own_core_gate()
    new, indices = deepcopy(old), []
    for index, node in enumerate(old["nodes"]):
        if node["kind"] != "FULL_PENDING":
            continue
        m = find_embedding(node["state"]["next"], node["state"]["faces"], proof)
        if m is not None:
            new["nodes"][index] = {
                "state": node["state"], "kind": "N24_SAME_ROOT_CORE",
                "core_to_actual_full_map": m, "own_core_proof_sha256": sha(COREPATH)}
            indices.append(index)
    assert indices
    new.update(same_root_core_leaf_indices=indices, own_same_root_core_proof_sha256=sha(COREPATH))
    result = check_mixed(old, new, constants, proof)
    assert not result["whole_family_strictly_closed"]
    assert result["same_root_nonstrict_complete_leaves"] == len(indices)
    assert result["pending_complete_leaves"] == oldpaid["pending_complete_leaves"]-len(indices)
    refused = []
    def reject(name, changed):
        try:
            check_mixed(old, changed, constants, proof)
        except (AssertionError, KeyError, ValueError, IndexError):
            refused.append(name)
        else:
            raise AssertionError("bad core disjunction accepted: "+name)
    for field, value in (
        ("N", 25), ("B", 16), ("cap8", 4058615), ("radius_upper", "1/4"),
        ("own_same_root_core_proof_sha256", "0"*64)):
        bad = deepcopy(new)
        bad[field] = value
        reject(field, bad)
    bad = deepcopy(new)
    index = indices[0]
    bad["nodes"][index]["core_to_actual_full_map"]["centers"][-1] = 14
    reject("wrong-actual-core-center-image", bad)
    bad = deepcopy(new)
    bad["nodes"][index]["own_core_proof_sha256"] = "0"*64
    reject("unbound-core-leaf-theorem", bad)
    bad = deepcopy(new)
    bad["same_root_core_leaf_indices"].pop()
    reject("missing-core-leaf-accounting", bad)
    bad = deepcopy(new)
    bad["nodes"][0] = deepcopy(bad["nodes"][index])
    reject("core-cannot-replace-a-topology-split", bad)
    bad = deepcopy(new)
    bad["nodes"].append(deepcopy(bad["nodes"][index]))
    reject("additional-unreachable-core-node", bad)
    output.mkdir()
    publish(output / "ORIGINAL-STRICT-CORE-CONTROL.json", old)
    publish(output / "MIXED-STRICT-CORE-CONTROL.json", new)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N24-own-core-complete-fiber-disjunction-controls-v1",
        "actual_complete_source_parent_index": parent["id"],
        "all_original_strict_branch_math_freshly_replayed_with_actual_full_core_leaves": True,
        "complete_unpaid_fiber_leaves": oldpaid["pending_complete_leaves"],
        "same_root_core_leaves": result["same_root_nonstrict_complete_leaves"],
        "unpaid_noncore_leaves_retained": result["pending_complete_leaves"],
        "actual_core_constraints_never_paid_as_strict_U24_exclusions": True,
        "all_original_topology_branch_cover_and_each_actual_full_core_map_replayed": True,
        "negative_scope_leaf_mapping_and_topology_controls_rejected": refused,
        "not_an_actual_production_worker_or_parent_adoption": True,
        "source_sha256": sha(Path(__file__)),
        "mixed_source_sha256": sha(ROOT / "mix_n24_core_family.py"),
        "own_core_transport_controls_sha256": sha(controlpath),
        "own_core_proof_sha256": sha(COREPATH),
        "original_control_sha256": sha(output / "ORIGINAL-STRICT-CORE-CONTROL.json"),
        "mixed_control_sha256": sha(output / "MIXED-STRICT-CORE-CONTROL.json"),
        "global_optimality_proved": False})
    print("N24 actual-source candidate complete-fiber core disjunction controls accepted:",
          oldpaid["pending_complete_leaves"], "full control leaves,", len(indices), "core,",
          result["pending_complete_leaves"], "honestly unpaid;", len(refused), "refusals", flush=True)


if __name__ == "__main__":
    main()
