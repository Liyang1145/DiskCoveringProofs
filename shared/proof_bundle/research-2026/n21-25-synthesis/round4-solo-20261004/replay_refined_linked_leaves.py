"""Stdlib-only same-topology refinement and fresh whole branch-tree acceptance."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish, bind, unchanged
from stream_catalog import sha
from linked_general_collar_kernel import replay

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("family", "refined", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    originalpath, originalreplay = args.family / "PROPOSAL.json", args.family / "EXACT.json"
    old, new, accepted = map(read, (originalpath, args.refined, originalreplay))
    assert accepted["verified"] and accepted["schema"] == "proof-paid-linked-general-collar-independent-replay-v1"
    assert accepted["source_sha256"] == sha(ROOT / "replay_linked_general_collar.py")
    unchanged(accepted["files_relative_to_workspace"])
    assert new["original_proposal_sha256"] == sha(originalpath)
    assert new["original_exact_replay_sha256"] == sha(originalreplay)
    assert new["refinement_source_sha256"] == sha(ROOT / "refine_linked_collar_leaves.py")
    assert new["only_original_FULL_PENDING_leaves_changed"]
    for field in ("schema", "N", "B", "collar_centers", "collar_faces", "roots", "constants_sha256",
                  "source_collar_sha256", "kernel_sha256", "source_sha256"):
        assert new[field] == old[field]
    assert len(new["nodes"]) == len(old["nodes"])
    changed = []
    for index, (a, b) in enumerate(zip(old["nodes"], new["nodes"], strict=True)):
        if a != b:
            assert a["kind"] == "FULL_PENDING" and b["state"] == a["state"]
            assert b["kind"] in ("FORCE", "ANGLE")
            changed.append(index)
    assert changed == new["refined_leaf_indices"]
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    assert new["constants_sha256"] == sha(constants_path)
    result = replay(args.refined, read(constants_path))
    files = {}
    for path in (Path(__file__), originalpath, originalreplay, args.refined,
                 ROOT / "refine_linked_collar_leaves.py", ROOT / "linked_general_collar_kernel.py",
                 ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md", constants_path, HIGH / "exact_graph.py"):
        bind(files, path)
    unchanged(files)
    publish(args.output, {**result, "schema": "same-topology-linked-collar-force-refinement-exact-v1",
                          "only_original_FULL_PENDING_leaves_changed": True,
                          "new_exact_leaf_payments": len(changed), "whole_tree_fresh_exact_replayed": True,
                          "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
                          "global_optimality_proved": False})
    print("Independent completed-leaf refinement:", len(changed), "new exact payments;",
          "whole fixed family paid:", result["all_full_simple_disk_completions_strictly_paid"], flush=True)


if __name__ == "__main__":
    main()
