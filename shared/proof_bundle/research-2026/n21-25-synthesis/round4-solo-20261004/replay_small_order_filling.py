"""Fresh stdlib-only own-order full completion disjunction acceptance."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from small_order_filling_kernel import replay_payload

assert __debug__


def replay(collarpath, proposalpath):
    collar, payload = read(collarpath), read(proposalpath)
    assert payload["source_collar_sha256"] == sha(collarpath)
    assert payload["source_sha256"] == sha(ROOT / "propose_small_order_filling.py")
    assert payload["kernel_sha256"] == sha(ROOT / "small_order_filling_kernel.py")
    assert (payload["N"], payload["B"], payload["collar_centers"], payload["collar_faces"]) == (
        collar["N"], collar["B"], collar["centers"], collar["faces"])
    N = collar["N"]
    constantspath = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
    assert payload["constants_sha256"] == sha(constantspath)
    frozen = {str(path.resolve()): sha(path) for path in (
        Path(__file__), collarpath, proposalpath, constantspath,
        ROOT / "propose_small_order_filling.py", ROOT / "small_order_filling_kernel.py",
        ROOT / "small_order_origin_caps.py", ROOT / "general_collar_filling.py",
        ROOT / "general_collar_filling_linked.py", ROOT / "complete_simple_collar.py",
        ROOT / "eight_rod_angles.py", ROOT / "angle_obstructions.py",
        ROOT / "SMALL-ORDER-COMPLETE-FILLING-SOURCE-v1.md",
        HIGH / "cross_order_strict_transfer.py", HIGH / "group_catalog.py",
        HIGH / "exact_graph.py", HIGH.parent / "round2-grouped/partial_force_exact.py")}
    result = replay_payload(payload, read(constantspath))
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    return {
        **result, "schema": "small-order-own-full-completion-independent-replay-v1",
        "source_sha256": sha(Path(__file__)), "frozen_files": frozen,
        "source_collar_sha256": sha(collarpath), "proposal_sha256": sha(proposalpath),
        "constants_sha256": sha(constantspath),
        "controls_and_actual_parent_adoption_still_required": True}


def main():
    ap = argparse.ArgumentParser()
    for name in ("collar", "proposal", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    result = replay(args.collar.resolve(), args.proposal.resolve())
    publish(args.output, result)
    print("Own-order full-family independent replay:", result["nodes"], "nodes; whole strict",
          result["whole_completion_family_strictly_closed"],
          "pending full/frontier", result["pending_complete_leaves"],
          result["unsearched_frontier_nodes"], flush=True)


if __name__ == "__main__":
    main()
