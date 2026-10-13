"""Standalone integer-cycle proposals and remaining changed-B candidate snapshot."""
from pathlib import Path
from collections import Counter
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from group_catalog import canonical, validate
from eight_rod_angles import constants_gate, exclusion

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.snapshot, args.output = args.snapshot.resolve(), args.output.resolve()
    assert args.snapshot.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists()
    snapshot = read(args.snapshot)
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    assert snapshot["source_theorems_not_reused_to_accept_changed_B_candidates"]
    assert snapshot["all_target_graphs_require_fresh_own_complete_angle_domain_proofs"]
    assert snapshot["source_sha256"] == sha(ROOT / "discover_boundary_contractions.py")
    assert snapshot["weak_graph_count"] == len(snapshot["weak_graphs"])
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constants_gate(constants)
    B, outcomes, remaining, remaining_ids, totals = snapshot["B"], [], [], [], Counter()
    assert snapshot["N"] == 25 and B in (15, 16)
    for index, graph in enumerate(snapshot["weak_graphs"]):
        centers, faces = graph["centers"], graph["faces"]
        code, mapping = canonical(centers, B, faces, 1)
        assert list(code) == faces and len(mapping["centers"]) == centers
        validate(centers, B, code, mapping, faces)
        candidate = exclusion(B, centers, faces, constants)
        outcome = {"source_candidate": index, "centers": centers, "faces": faces,
                   "status": "own-B-integer-cycle-excluded" if candidate is not None else "pending"}
        if candidate is not None:
            outcome.update(candidate)
        else:
            remaining.append(graph);remaining_ids.append(index)
        totals[outcome["status"]] += 1
        outcomes.append(outcome)
    files = {}
    for path in (Path(__file__), args.snapshot, constants_path, ROOT / "eight_rod_angles.py",
                 ROOT / "EIGHT-ROD-ANGLE-SOURCE.md", ROOT / "n25-eight-rod-exact-cap-20261005-v1.json",
                 ROOT / "discover_boundary_contractions.py"):
        bind(files, path)
    unchanged(files)
    args.output.mkdir()
    publish(args.output / "ANGLE-PROPOSAL.json", {
        "schema": "changed-B-candidate-own-angle-proposals-v1", "N": 25, "B": B,
        "source_snapshot_sha256": sha(args.snapshot), "source_candidates": len(outcomes),
        "constants_sha256": sha(constants_path), "outcomes": outcomes, "totals": dict(totals),
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    publish(args.output / "REMAINING.json", {
        "schema": "incomplete-collar-discovery-v1", "N": 25, "B": B,
        "weak_graph_count": len(remaining), "weak_graphs": remaining, "original_candidate_indices": remaining_ids,
        "source_candidate_snapshot_sha256": sha(args.snapshot), "source_sha256": sha(Path(__file__)),
        "force_tree_proposals_still_required": True, "no_negative_eight_rod_cycle_found_during_proposal": True,
        "no_match_is_not_a_realization_or_an_exclusion": True,
        "complete_necessary_outer_search": False, "complete_family_coverage": False,
        "global_optimality_proved": False,
    })
    print("Changed-B own-domain angle proposals:", dict(totals),
          "; independent cycle replay still required", flush=True)


if __name__ == "__main__":
    main()
