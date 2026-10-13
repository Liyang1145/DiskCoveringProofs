"""Independent stdlib-only fixed-hole exact disjunction acceptance."""
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
    ap.add_argument("--collar", type=Path, required=True)
    ap.add_argument("--proposal", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    collar, payload = read(args.collar), read(args.proposal)
    assert payload["source_collar_sha256"] == sha(args.collar)
    assert payload["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
    assert payload["source_sha256"] == sha(ROOT / "prove_linked_general_collar.py")
    assert (payload["N"], payload["B"], payload["collar_centers"], payload["collar_faces"]) == (
        collar["N"], collar["B"], collar["centers"], collar["faces"])
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    assert payload["constants_sha256"] == sha(constants_path)
    result = replay(args.proposal, read(constants_path))
    files = {}
    for path in (
        Path(__file__), args.collar, args.proposal, constants_path, ROOT / "linked_general_collar_kernel.py",
        ROOT / "prove_linked_general_collar.py", ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md", ROOT / "general_collar_filling.py", ROOT / "general_collar_filling_linked.py",
        ROOT / "linked-general-paid-collar-source-derivation.json",
        ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md", ROOT / "general-paid-collar-source-derivation.json",
        ROOT / "CLOSED-BOUNDARY-FAN-TRANSFER.md", ROOT / "eight_rod_angles.py",
        HIGH / "exact_graph.py", HIGH.parent / "round2-grouped/partial_force_exact.py",
        HIGH / "cross_order_strict_transfer.py",
    ):
        bind(files, path)
    unchanged(files)
    publish(args.output, {**result, "schema": "proof-paid-linked-general-collar-independent-replay-v1",
                          "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
                          "all_related_full_completions_not_enumerated_individually": True,
                          "controls_and_source_induction_gate_still_required": True,
                          "global_optimality_proved": False})
    print("Independent paid-hole replay:", result["nodes"], "nodes;",
          "all fixed-family completions paid:", result["all_full_simple_disk_completions_strictly_paid"],
          "; pending full/frontier:", result["pending_complete_leaves"], result["unsearched_frontier_nodes"], flush=True)


if __name__ == "__main__":
    main()
