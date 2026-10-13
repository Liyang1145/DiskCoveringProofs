"""Actual original full leaves: own strict refinement then own nonstrict core."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha
from refine_small_order_family import original_gate, refinement_shape
from small_order_filling_kernel import constants_gate, angle_exclusion, replay_payload
from n24_actual_core_transport import own_core_gate, find_embedding, validate_embedding, COREPATH, SYSTEMPATH
from mix_n24_core_family import check_mixed, controls_gate

assert __debug__


def propose(family, controls, output, force_limit):
    assert not output.exists() and 31 < force_limit <= 10001
    controls_gate(controls)
    old, accepted, constants, _ = original_gate(family)
    assert (old["N"], old["B"]) == (24, 15)
    proof, strict, changes, cache, coremaps = own_core_gate(), deepcopy(old), [], {}, {}
    cap8 = constants_gate(constants, 24, 15)
    from probe_collar_batches import make
    import exact_graph as exact
    for index, node in enumerate(old["nodes"]):
        if node["kind"] != "FULL_PENDING":
            continue
        state = node["state"]
        mapping = find_embedding(state["next"], state["faces"], proof)
        if mapping is not None:
            validate_embedding(mapping, state["next"], state["faces"], proof)
            coremaps[index] = mapping
            print("Own N24 complete leaf preserved for same-root core", index, flush=True)
            continue
        key = (state["next"], tuple(state["faces"]))
        if key not in cache:
            payment = angle_exclusion(15, state["next"], state["faces"], constants, cap8)
            if payment is None:
                nodes, _ = make(15, state["next"], state["faces"], constants, force_limit, route_weak=False)
                if nodes is not None:
                    payment = {"kind": "FORCE", "force_nodes": nodes,
                               "exact_result": exact.verify(
                                   15, state["next"], state["faces"], nodes, constants)}
            cache[key] = payment
        if cache[key] is not None:
            strict["nodes"][index] = {"state": state, **cache[key]}
            changes.append(index)
        print("Own N24 noncore complete leaf deeper strict", index, cache[key] is not None, flush=True)
    assert coremaps
    strict.update(refined_leaf_indices=changes, only_original_FULL_PENDING_leaves_changed=True)
    refinement_shape(old, strict)
    mixed = deepcopy(strict)
    for index, mapping in coremaps.items():
        mixed["nodes"][index] = {
            "state": old["nodes"][index]["state"], "kind": "N24_SAME_ROOT_CORE",
            "core_to_actual_full_map": mapping, "own_core_proof_sha256": sha(COREPATH)}
    mixed.update(same_root_core_leaf_indices=sorted(coremaps),
                 own_same_root_core_proof_sha256=sha(COREPATH))
    for path, digest in accepted["frozen_files"].items():
        assert sha(path) == digest
    publish(output, {
        "schema": "N24-actual-original-complete-family-strict-refined-plus-own-core-proposal-v1",
        "N": 24, "B": 15, "strict_refined": strict, "strict_and_core": mixed,
        "original_proposal_sha256": sha(family / "PROPOSAL.json"),
        "original_exact_report_sha256": sha(family / "EXACT.json"),
        "actual_source_collar_sha256": sha(family / "INPUT-COLLAR.json"),
        "core_transport_controls_sha256": sha(controls), "own_core_proof_sha256": sha(COREPATH),
        "source_sha256": sha(Path(__file__)), "force_limit": force_limit,
        "original_inner_source_fields_retained_only_as_original_history": True,
        "formal_complete_parent_adoption_still_required": True, "global_optimality_proved": False})


def combined_shape(old, payload):
    assert payload["schema"] == "N24-actual-original-complete-family-strict-refined-plus-own-core-proposal-v1"
    assert (payload["N"], payload["B"]) == (24, 15)
    strict, mixed = payload["strict_refined"], payload["strict_and_core"]
    changed = refinement_shape(old, strict)
    assert payload["original_inner_source_fields_retained_only_as_original_history"]
    return strict, mixed, changed


def audit(family, controls, proposalpath):
    controls_gate(controls)
    old, accepted, constants, constantspath = original_gate(family)
    payload, proof = read(proposalpath), own_core_gate()
    assert payload["source_sha256"] == sha(Path(__file__))
    assert payload["original_proposal_sha256"] == sha(family / "PROPOSAL.json")
    assert payload["original_exact_report_sha256"] == sha(family / "EXACT.json")
    assert payload["actual_source_collar_sha256"] == sha(family / "INPUT-COLLAR.json")
    assert payload["core_transport_controls_sha256"] == sha(controls)
    assert payload["own_core_proof_sha256"] == sha(COREPATH)
    strict, mixed, changed = combined_shape(old, payload)
    strict_result = replay_payload(strict, constants)
    result = check_mixed(strict, mixed, constants, proof)
    assert strict_result["unsearched_frontier_nodes"] == 0
    assert strict_result["pending_complete_leaves"] == result["pending_complete_leaves"]+result["same_root_nonstrict_complete_leaves"]
    frozen = dict(accepted["frozen_files"])
    for path, digest in proof["frozen_files"].items():
        assert path not in frozen or frozen[path] == digest
        frozen[path] = digest
    for path in (
        Path(__file__), controls, proposalpath, family / "PROPOSAL.json", family / "EXACT.json",
        family / "INPUT-COLLAR.json", constantspath, COREPATH, SYSTEMPATH,
        ROOT / "refine_small_order_family.py", ROOT / "mix_n24_core_family.py",
        ROOT / "n24_actual_core_transport.py", ROOT / "small_order_filling_kernel.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    return {
        **result, "schema": "N24-actual-complete-family-finer-strict-plus-own-nonstrict-core-independent-replay-v1",
        "new_strict_complete_leaf_payments": len(changed),
        "original_actual_full_family_identity_and_both_refinement_layers_checked": True,
        "original_core_mathematics_honestly_reused_not_new69215_node_replay": True,
        "source_collar_sha256": sha(family / "INPUT-COLLAR.json"),
        "original_proposal_sha256": sha(family / "PROPOSAL.json"),
        "original_exact_report_sha256": sha(family / "EXACT.json"),
        "proposal_sha256": sha(proposalpath), "own_core_proof_sha256": sha(COREPATH),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__))}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--audit", action="store_true")
    for name in ("family", "controls", "output"):
        ap.add_argument("--"+name, required=True, type=Path)
    ap.add_argument("--proposal", type=Path)
    ap.add_argument("--force-limit", type=int, default=511)
    args = ap.parse_args()
    family, controls, output = (getattr(args, key).resolve() for key in ("family", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (family, controls, output)) and not output.exists()
    if args.audit:
        assert args.proposal is not None
        result = audit(family, controls, args.proposal.resolve())
        publish(output, result)
        print("Actual whole N24 family finer-strict+own-core accepted:", result["new_strict_complete_leaf_payments"],
              "new strict", result["same_root_nonstrict_complete_leaves"], "core",
              "remaining", result["pending_complete_leaves"],
              "whole paid", result["whole_completion_family_paid_strict_or_same_root"], flush=True)
    else:
        propose(family, controls, output, args.force_limit)


if __name__ == "__main__":
    main()
