"""Refine only already-replayed FULL_PENDING leaves; preserve topology and old payments."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish, unchanged
from stream_catalog import sha
from probe_groups import make
import exact_graph as exact
from eight_rod_angles import exclusion

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("family", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--force-limit", type=int, default=31)
    args = ap.parse_args()
    family, output = args.family.resolve(), args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    oldpath, replaypath = family / "PROPOSAL.json", family / "EXACT.json"
    old, accepted = read(oldpath), read(replaypath)
    assert accepted["verified"] and accepted["schema"] == "proof-paid-linked-general-collar-independent-replay-v1"
    assert accepted["source_sha256"] == sha(ROOT / "replay_linked_general_collar.py")
    unchanged(accepted["files_relative_to_workspace"])
    assert accepted["pending_complete_leaves"] > 0 and accepted["unsearched_frontier_nodes"] == 0
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert old["constants_sha256"] == sha(constants_path)
    new, changed, cache = deepcopy(old), [], {}
    for index, node in enumerate(old["nodes"]):
        if node["kind"] != "FULL_PENDING":
            continue
        state = node["state"]
        key = (state["next"], tuple(state["faces"]))
        if key not in cache:
            angle = exclusion(old["B"], state["next"], state["faces"], constants)
            if angle is not None:
                cache[key] = {"kind": "ANGLE", **angle}
            else:
                force_nodes, diagnostic = make(old["B"], state["next"], state["faces"], constants,
                                               args.force_limit, route_weak=False)
                if force_nodes is None:
                    cache[key] = None
                else:
                    checked = exact.verify(old["B"], state["next"], state["faces"], force_nodes, constants)
                    cache[key] = {"kind": "FORCE", "force_nodes": force_nodes, "exact_result": checked}
        if cache[key] is not None:
            new["nodes"][index] = {"state": state, **cache[key]}
            changed.append(index)
        print("Refined completed leaf:", index, "paid:", cache[key] is not None, flush=True)
    new.update(original_proposal_sha256=sha(oldpath), original_exact_replay_sha256=sha(replaypath),
               refinement_source_sha256=sha(Path(__file__)), refined_leaf_indices=changed,
               refinement_force_limit=args.force_limit,
               only_original_FULL_PENDING_leaves_changed=True, global_optimality_proved=False)
    publish(output, new)
    print("Force refinement candidate produced:", len(changed), "newly paid leaves; independent replay required", flush=True)


if __name__ == "__main__":
    main()
