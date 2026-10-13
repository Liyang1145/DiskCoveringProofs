"""Own complete-family strict/core disjunction, not a geometric weak exclusion."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha
from refine_small_order_family import original_gate
from small_order_filling_kernel import replay_payload, children, constants_gate
from n24_actual_core_transport import own_core_gate, validate_embedding, find_embedding, COREPATH, SYSTEMPATH

assert __debug__


def mixed_shape(old, new):
    for field in (
        "schema", "N", "B", "collar_centers", "collar_faces", "roots", "radius_upper",
        "cap8", "constants_sha256", "source_collar_sha256", "kernel_sha256", "source_sha256"):
        assert new[field] == old[field]
    assert (new["N"], new["B"]) == (24, 15)
    assert len(new["nodes"]) == len(old["nodes"])
    changed = []
    for index, (a, b) in enumerate(zip(old["nodes"], new["nodes"], strict=True)):
        if a != b:
            assert a["kind"] == "FULL_PENDING" and b["state"] == a["state"]
            assert b["kind"] == "N24_SAME_ROOT_CORE"
            assert set(b) == {"kind", "state", "core_to_actual_full_map", "own_core_proof_sha256"}
            changed.append(index)
    assert changed == new["same_root_core_leaf_indices"]
    return changed


def check_mixed(old, new, constants, proof):
    indices = mixed_shape(old, new)
    constants_gate(constants, 24, 15)
    assert indices and new["own_same_root_core_proof_sha256"] == sha(COREPATH)
    proxy = deepcopy(new)
    for index in indices:
        node = new["nodes"][index]
        assert node["own_core_proof_sha256"] == sha(COREPATH)
        assert children(node["state"], 24, 15) is None, "core payment requires an actual complete simple disk"
        validate_embedding(node["core_to_actual_full_map"],
                           node["state"]["next"], node["state"]["faces"], proof)
        # The strict replayer checks the identical entire topology/strict
        # branches; these explicitly unpaid placeholders are then paid only
        # by the independently validated own exact core theorem above.
        proxy["nodes"][index] = {"state": node["state"], "kind": "FRONTIER"}
    result = replay_payload(proxy, constants)
    assert result["unsearched_frontier_nodes"] == len(indices), "no original unknown topology can be paid by core"
    return {
        **result, "schema": "N24-complete-family-own-strict-and-same-root-core-independent-replay-v1",
        "same_root_nonstrict_complete_leaves": len(indices), "unsearched_frontier_nodes": 0,
        "whole_completion_family_paid_strict_or_same_root": result["pending_complete_leaves"] == 0,
        "whole_family_strictly_closed": False,
        "core_payments_never_recast_as_strict_U24_exclusions": True,
        "every_actual_complete_core_face_center_anchor_and_witness_rod_mapped": True,
        "all_other_original_branches_and_exact_math_freshly_replayed": True,
        "not_a_standalone_weak_geometric_exclusion": True,
        "actual_complete_parent_adoption_still_required": True,
        "global_optimality_proved": False}


def controls_gate(path):
    controls = read(path)
    assert controls["verified"]
    assert controls["schema"] == "N24-own-core-full-type-subgraph-transport-controls-and-attaining-parent-identity-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n24_core_transport.py")
    assert controls["transport_source_sha256"] == sha(ROOT / "n24_actual_core_transport.py")
    assert controls["own_nonstrict_core_proof_sha256"] == sha(COREPATH)
    assert len(controls["negative_actual_core_transport_controls_rejected"]) == 8


def propose(family, controls, output):
    assert not output.exists()
    controls_gate(controls)
    old, accepted, _, _ = original_gate(family)
    assert (old["N"], old["B"]) == (24, 15)
    proof = own_core_gate()
    new, indices = deepcopy(old), []
    for index, node in enumerate(old["nodes"]):
        if node["kind"] != "FULL_PENDING":
            continue
        state = node["state"]
        mapping = find_embedding(state["next"], state["faces"], proof)
        if mapping is None:
            continue
        validate_embedding(mapping, state["next"], state["faces"], proof)
        new["nodes"][index] = {
            "state": state, "kind": "N24_SAME_ROOT_CORE", "core_to_actual_full_map": mapping,
            "own_core_proof_sha256": sha(COREPATH)}
        indices.append(index)
    assert indices, "no own core complete leaf found; do not claim a mixed payment"
    new.update(
        same_root_core_leaf_indices=indices, own_same_root_core_proof_sha256=sha(COREPATH),
        original_proposal_sha256=sha(family / "PROPOSAL.json"),
        original_exact_replay_sha256=sha(family / "EXACT.json"),
        actual_source_collar_sha256=sha(family / "INPUT-COLLAR.json"),
        core_transport_controls_sha256=sha(controls),
        mixed_source_sha256=sha(Path(__file__)),
        original_source_field_retained_only_as_original_history=True,
        complete_parent_adoption_not_performed_here=True,
        global_optimality_proved=False)
    mixed_shape(old, new)
    for path, digest in accepted["frozen_files"].items():
        assert sha(path) == digest
    publish(output, new)


def audit(family, controls, mixedpath):
    controls_gate(controls)
    old, accepted, constants, _ = original_gate(family)
    new, proof = read(mixedpath), own_core_gate()
    assert new["mixed_source_sha256"] == sha(Path(__file__))
    assert new["original_proposal_sha256"] == sha(family / "PROPOSAL.json")
    assert new["original_exact_replay_sha256"] == sha(family / "EXACT.json")
    assert new["actual_source_collar_sha256"] == sha(family / "INPUT-COLLAR.json")
    assert new["core_transport_controls_sha256"] == sha(controls)
    result = check_mixed(old, new, constants, proof)
    files = dict(accepted["frozen_files"])
    files.update(proof["frozen_files"])
    for path in (
        Path(__file__), controls, mixedpath, family / "PROPOSAL.json",
        family / "EXACT.json", family / "INPUT-COLLAR.json", COREPATH, SYSTEMPATH,
        ROOT / "n24_actual_core_transport.py", ROOT / "small_order_filling_kernel.py"):
        files[str(path)] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    return {
        **result, "own_nonstrict_core_mathematics_honestly_reused_not_new69215_node_replay": True,
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "mixed_proposal_sha256": sha(mixedpath),
        "original_exact_report_sha256": sha(family / "EXACT.json")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--audit", action="store_true")
    ap.add_argument("--family", required=True, type=Path)
    ap.add_argument("--controls", required=True, type=Path)
    ap.add_argument("--mixed", type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    family, controls, output = (getattr(args, key).resolve() for key in ("family", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (family, controls, output)) and not output.exists()
    if args.audit:
        assert args.mixed is not None
        result = audit(family, controls, args.mixed.resolve())
        publish(output, result)
        print("N24 actual complete-family strict/own-core fresh replay:", result["same_root_nonstrict_complete_leaves"],
              "core leaves, remaining", result["pending_complete_leaves"],
              "whole paid", result["whole_completion_family_paid_strict_or_same_root"], flush=True)
    else:
        propose(family, controls, output)


if __name__ == "__main__":
    main()
