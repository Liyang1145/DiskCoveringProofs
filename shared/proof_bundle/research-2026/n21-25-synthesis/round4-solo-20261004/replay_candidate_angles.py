"""Independent own-B cycle checks; does not accept the candidate generator as proof."""
from pathlib import Path
from collections import Counter
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from eight_rod_angles import constants_gate, verify_cycle

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for key in ("snapshot", "proposal", "output"):
        ap.add_argument("--"+key, type=Path, required=True)
    args = ap.parse_args()
    for key in vars(args):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists()
    snapshot, proposal = read(args.snapshot), read(args.proposal)
    assert proposal["schema"] == "changed-B-candidate-own-angle-proposals-v1"
    assert proposal["source_sha256"] == sha(ROOT / "split_candidate_angles.py")
    assert proposal["source_snapshot_sha256"] == sha(args.snapshot)
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    N, B = proposal["N"], proposal["B"]
    assert (snapshot["N"], snapshot["B"]) == (N, B) and N == 25 and B in (15, 16)
    assert proposal["source_candidates"] == len(proposal["outcomes"]) == snapshot["weak_graph_count"]
    assert len(snapshot["weak_graphs"]) == snapshot["weak_graph_count"]
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constants_gate(constants)
    assert proposal["constants_sha256"] == sha(constants_path)
    totals = Counter()
    for index, (graph, outcome) in enumerate(zip(snapshot["weak_graphs"], proposal["outcomes"], strict=True)):
        assert outcome["source_candidate"] == index
        assert (outcome["centers"], outcome["faces"]) == (graph["centers"], graph["faces"])
        if outcome["status"] == "own-B-integer-cycle-excluded":
            result = verify_cycle(B, graph["centers"], graph["faces"], outcome["cycle"], constants)
            assert result == outcome["exact_cycle_check"] and result["negative_integer_sum"] < 0
        else:
            assert outcome["status"] == "pending"
        totals[outcome["status"]] += 1
    assert dict(totals) == proposal["totals"]
    files = dict(proposal["files_relative_to_workspace"])
    unchanged(files)
    for path in (Path(__file__), args.snapshot, args.proposal, constants_path, ROOT / "eight_rod_angles.py",
                 ROOT / "EIGHT-ROD-ANGLE-SOURCE.md"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(args.output, {
        "verified": True, "schema": "changed-B-own-domain-integer-cycle-exact-replay-v1",
        "N": N, "B": B, "source_candidate_count": snapshot["weak_graph_count"], "totals": dict(totals),
        "all_positive_cycles_individually_own_B_checked": True,
        "changed_B_source_certificates_not_used_as_acceptance": True,
        "source_proposal_sha256": sha(args.proposal), "source_snapshot_sha256": sha(args.snapshot),
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "no_optimizer_imported": True, "not_a_complete_competitor_family_or_union": True,
        "global_optimality_proved": False,
    })
    print("Changed-B own-angle independent acceptance PASS:", dict(totals), flush=True)


if __name__ == "__main__":
    main()
