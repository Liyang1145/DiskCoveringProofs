"""Propose deeper trees only on earlier actual full-type proposal pendings."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import os
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from probe_collar_batches import make
import exact_graph as exact

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("restored", "previous-stage", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, required=True)
    args = ap.parse_args()
    restored, previous, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("restored", "previous-stage", "output"))
    assert all(path.is_relative_to(ROOT) for path in (restored, previous, output))
    assert not output.exists() and 31 < args.limit <= 10001
    accepted, old, inputs = map(read, (
        restored / "VERIFIED.json", previous / "SUMMARY.json", previous / "INPUT-BINDINGS.json"))
    assert accepted["verified"]
    assert accepted["schema"] == "original-N23-B15-actual-complete-residual-types-restoration-v1"
    assert accepted["source_sha256"] == sha(ROOT / "extract_n23_actual_residual_types.py")
    assert old["source_sha256"] in (
        sha(ROOT / "propose_n23_actual_full_types.py"), sha(Path(__file__)))
    assert old["input_bindings_sha256"] == sha(previous / "INPUT-BINDINGS.json")
    assert old["outcomes_sha256"] == sha(previous / "OUTCOMES.jsonl")
    assert old["actual_full_types_processed"] == accepted["actual_full_residual_types"]
    assert args.limit > inputs["force_limit"]
    fullpath = restored / accepted["full_types_file"]
    fullhash = sha(fullpath)
    assert fullpath.resolve().is_relative_to(restored)
    assert fullhash == accepted["full_types_sha256"] == inputs["restored_full_types_sha256"]
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    frozen = {str(path): sha(path) for path in (
        Path(__file__), restored / "VERIFIED.json", fullpath,
        previous / "SUMMARY.json", previous / "INPUT-BINDINGS.json",
        previous / "OUTCOMES.jsonl", constantspath,
        ROOT / "propose_n23_actual_full_types.py", ROOT / "probe_collar_batches.py",
        HIGH / "candidate_domain.py", HIGH / "exact_graph.py", Path(exact.kernel.__file__))}
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 23, "B": 15, "force_limit": args.limit,
        "restored_full_types_sha256": fullhash,
        "restoration_report_sha256": sha(restored / "VERIFIED.json"),
        "candidate_full_faces": inputs["candidate_full_faces"],
        "all_faces_retained_not_outer_only": True,
        "previous_proposal_positive_types_not_reproposed": True,
        "previous_known_full_candidate_never_strictly_reproposed": True,
        "previous_stage_report_sha256": sha(previous / "SUMMARY.json"),
        "previous_stage_path": str(previous), "frozen_files": frozen,
        "selection_is_previous_proposal_pending_not_formal_parent_payment_claim": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    counts, oldcounts, newcounts = Counter(), Counter(), Counter()
    previousindex, started = -1, time.monotonic()
    with fullpath.open(encoding="ascii") as source, \
            (previous / "OUTCOMES.jsonl").open(encoding="ascii") as previousrows, \
            (output / "OUTCOMES.jsonl").open("x", encoding="ascii") as ledger:
        for line in source:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            index = row["index"]
            assert type(index) is int and index > previousindex
            previousindex = index
            previousline = previousrows.readline()
            assert previousline
            before = json.loads(previousline, object_pairs_hook=no_duplicate_keys)
            assert before["index"] == index and before["outer_group"] == row["outer_group"]
            oldcounts[before["status"]] += 1
            if before["status"] == "strict":
                treepath = (
                    previous / before["certificate_path_relative_to_receipt"]
                    if "certificate_path_relative_to_receipt" in before
                    else previous / f"type-{index:08}.json.gz").resolve()
                assert treepath.is_relative_to(ROOT)
                assert sha(treepath) == before["tree_sha256"]
                frozen[str(treepath)] = sha(treepath)
                outcome = {**before, "certificate_path_relative_to_receipt": os.path.relpath(treepath, output)}
            elif before["status"] == "exact-candidate-full-type-retained":
                outcome = before
            else:
                assert before["status"] == "pending"
                nodes, failure = make(15, 23, row["faces"], constants, args.limit)
                if nodes is None:
                    outcome = {"index": index, "outer_group": row["outer_group"],
                               "status": "pending", **failure}
                else:
                    result = exact.verify(15, 23, row["faces"], nodes, constants)
                    assert F(result["minimum_force_margin"]) > 0
                    treepath = output / f"type-{index:08}.json.gz"
                    with gzip.open(treepath, "xt", encoding="utf8") as treefile:
                        json.dump({
                            "N": 23, "B": 15, "full_centers": 23, "index": index,
                            "faces": row["faces"], "nodes": nodes,
                            "restored_full_types_sha256": fullhash,
                            "constants_sha256": constantshash,
                            "radius_upper": constants["radius_upper"],
                        }, treefile, separators=(",", ":"))
                    outcome = {"index": index, "outer_group": row["outer_group"],
                               "status": "strict", "tree_sha256": sha(treepath),
                               "exact_result": result}
                newcounts[outcome["status"]] += 1
                print("N23 actual full-type deeper pending proposal", sum(newcounts.values()),
                      "limit", args.limit, dict(newcounts), "seconds",
                      round(time.monotonic()-started, 1), flush=True)
            counts[outcome["status"]] += 1
            ledger.write(json.dumps(outcome, separators=(",", ":"))+"\n")
            ledger.flush()
        assert not previousrows.read(1)
    assert dict(oldcounts) == old["counts"]
    assert sum(counts.values()) == old["actual_full_types_processed"]
    assert sum(newcounts.values()) == oldcounts["pending"]
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "SUMMARY.json", {
        "N": 23, "B": 15, "actual_full_types_processed": sum(counts.values()),
        "counts": dict(counts), "selected_prior_pending_full_types": sum(newcounts.values()),
        "new_proposal_counts": dict(newcounts),
        "old_positive_actual_type_trees_bound_not_reproposed": oldcounts["strict"],
        "outcomes_sha256": sha(output / "OUTCOMES.jsonl"),
        "input_bindings_sha256": sha(output / "INPUT-BINDINGS.json"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "successor_independent_replay_and_actual_parent_payment_adoption_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23 deeper actual complete-type proposal ended:", dict(newcounts),
          "; no new formal source payment here", flush=True)


if __name__ == "__main__":
    main()
