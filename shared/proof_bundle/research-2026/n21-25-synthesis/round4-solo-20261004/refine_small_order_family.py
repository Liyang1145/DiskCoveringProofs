"""Only original FULL_PENDING leaves change; own-order full-tree reacceptance."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha
from small_order_filling_kernel import constants_gate, angle_exclusion, replay_payload

assert __debug__


def original_gate(family):
    oldpath, exactpath, collarpath = (
        family / "PROPOSAL.json", family / "EXACT.json", family / "INPUT-COLLAR.json")
    old, accepted, collar = map(read, (oldpath, exactpath, collarpath))
    assert accepted["verified"]
    assert accepted["schema"] == "small-order-own-full-completion-independent-replay-v1"
    assert accepted["source_sha256"] == sha(ROOT / "replay_small_order_filling.py")
    assert accepted["pending_complete_leaves"] > 0 and accepted["unsearched_frontier_nodes"] == 0
    assert not accepted["whole_completion_family_strictly_closed"]
    assert old["schema"] == "small-order-own-constant-complete-collar-branch-tree-v1"
    assert old["N"] in (23, 24) and old["N"] == collar["N"]
    assert old["source_sha256"] == sha(ROOT / "propose_small_order_filling.py")
    assert old["kernel_sha256"] == sha(ROOT / "small_order_filling_kernel.py")
    assert old["source_collar_sha256"] == sha(collarpath)
    assert (old["B"], old["collar_centers"], old["collar_faces"]) == (
        collar["B"], collar["centers"], collar["faces"])
    constants_path = ROOT.parent / f"evidence/core-reduction/constants/n{old['N']}.json"
    constants = read(constants_path)
    constants_gate(constants, old["N"], old["B"])
    assert old["constants_sha256"] == sha(constants_path)
    for path, digest in accepted["frozen_files"].items():
        assert sha(path) == digest
    return old, accepted, constants, constants_path


def refinement_shape(old, new):
    for field in (
        "schema", "N", "B", "collar_centers", "collar_faces", "roots", "radius_upper",
        "cap8", "constants_sha256", "source_collar_sha256", "kernel_sha256", "source_sha256"):
        assert new[field] == old[field]
    assert new["only_original_FULL_PENDING_leaves_changed"]
    assert len(new["nodes"]) == len(old["nodes"])
    changed = []
    for index, (before, after) in enumerate(zip(old["nodes"], new["nodes"], strict=True)):
        if before != after:
            assert before["kind"] == "FULL_PENDING"
            assert before["state"] == after["state"]
            assert after["kind"] in ("FORCE", "ANGLE")
            changed.append(index)
    assert changed == new["refined_leaf_indices"]
    return changed


def propose(family, output, force_limit):
    assert not output.exists() and 31 < force_limit <= 10001
    old, accepted, constants, constantspath = original_gate(family)
    from probe_collar_batches import make
    import exact_graph as exact
    new, cache, changed = deepcopy(old), {}, []
    cap8 = constants_gate(constants, old["N"], old["B"])
    for index, node in enumerate(old["nodes"]):
        if node["kind"] != "FULL_PENDING":
            continue
        state = node["state"]
        key = (state["next"], tuple(state["faces"]))
        if key not in cache:
            value = angle_exclusion(old["B"], state["next"], state["faces"], constants, cap8)
            if value is None:
                force_nodes, _ = make(old["B"], state["next"], state["faces"],
                                      constants, force_limit, route_weak=False)
                if force_nodes is not None:
                    value = {
                        "kind": "FORCE", "force_nodes": force_nodes,
                        "exact_result": exact.verify(
                            old["B"], state["next"], state["faces"], force_nodes, constants)}
            cache[key] = value
        if cache[key] is not None:
            new["nodes"][index] = {"state": state, **cache[key]}
            changed.append(index)
        print("Own-order completed leaf refinement", index, "new strict proof",
              cache[key] is not None, flush=True)
    new.update(
        original_proposal_sha256=sha(family / "PROPOSAL.json"),
        original_exact_replay_sha256=sha(family / "EXACT.json"),
        refinement_source_sha256=sha(Path(__file__)),
        refined_leaf_indices=changed, refinement_force_limit=force_limit,
        only_original_FULL_PENDING_leaves_changed=True,
        original_source_sha256_retained_only_as_original_history_not_refinement_authorship=True,
        complete_parent_adoption_not_performed_here=True,
        global_optimality_proved=False)
    refinement_shape(old, new)
    for path, digest in accepted["frozen_files"].items():
        assert sha(path) == digest
    publish(output, new)


def audit(family, refinedpath):
    old, accepted, constants, constantspath = original_gate(family)
    new = read(refinedpath)
    assert new["original_proposal_sha256"] == sha(family / "PROPOSAL.json")
    assert new["original_exact_replay_sha256"] == sha(family / "EXACT.json")
    assert new["refinement_source_sha256"] == sha(Path(__file__))
    assert new["original_source_sha256_retained_only_as_original_history_not_refinement_authorship"]
    changed = refinement_shape(old, new)
    result = replay_payload(new, constants)
    frozen = dict(accepted["frozen_files"])
    for path in (
        Path(__file__), refinedpath, family / "PROPOSAL.json", family / "EXACT.json",
        family / "INPUT-COLLAR.json", constantspath, ROOT / "small_order_filling_kernel.py",
        ROOT / "SMALL-ORDER-COMPLETE-FILLING-SOURCE-v1.md"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    return {
        **result, "schema": "small-order-same-topology-leaf-refinement-independent-replay-v1",
        "new_exact_leaf_payments": len(changed), "only_original_FULL_PENDING_leaves_changed": True,
        "whole_original_completion_branch_tree_freshly_independently_math_replayed": True,
        "original_proposal_sha256": sha(family / "PROPOSAL.json"),
        "original_exact_report_sha256": sha(family / "EXACT.json"),
        "refined_proposal_sha256": sha(refinedpath), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "actual_complete_parent_adoption_still_required": True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--audit", action="store_true")
    ap.add_argument("--family", required=True, type=Path)
    ap.add_argument("--refined", type=Path)
    ap.add_argument("--output", required=True, type=Path)
    ap.add_argument("--force-limit", type=int, default=511)
    args = ap.parse_args()
    family, output = args.family.resolve(), args.output.resolve()
    assert family.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    if args.audit:
        assert args.refined is not None
        result = audit(family, args.refined.resolve())
        publish(output, result)
        print("Own-order complete same-topology deep replay; whole strict",
              result["whole_completion_family_strictly_closed"],
              "pending", result["pending_complete_leaves"], flush=True)
    else:
        propose(family, output, args.force_limit)


if __name__ == "__main__":
    main()
