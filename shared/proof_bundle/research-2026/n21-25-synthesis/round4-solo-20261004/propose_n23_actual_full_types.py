"""Strict force proposals on restored complete types, not their outer graphs."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from n22_core_case import propose_canonical_map
from audit_streamed_hierarchy import check_map
from probe_collar_batches import make
import exact_graph as exact

assert __debug__


def full_candidate_map(full, candidate):
    """Proposal only: independently checked complete-face bijection if found."""
    code, candidate_map = propose_canonical_map(23, 15, candidate)
    actualcode, actual_map = propose_canonical_map(23, 15, full)
    if code != actualcode:
        return None
    inverse = {v: j for j, v in enumerate(actual_map["centers"])}
    center = [inverse[v] for v in candidate_map["centers"]]
    sign = candidate_map["orientation"]*actual_map["orientation"]
    shift = center[0]
    mapping = {"centers": center, "anchors": [
        (shift+sign*j-(sign < 0)) % 15 for j in range(15)],
        "orientation": sign, "shift": shift}
    check_map(23, 15, {"centers": 23, "faces": candidate}, mapping, set(full), 0)
    return mapping


def main():
    ap = argparse.ArgumentParser()
    for name in ("restored", "core", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, required=True)
    args = ap.parse_args()
    restored, corepath, output = args.restored.resolve(), args.core.resolve(), args.output.resolve()
    assert all(path.is_relative_to(ROOT) for path in (restored, corepath, output))
    assert not output.exists() and 1 <= args.limit <= 5001
    accepted = read(restored / "VERIFIED.json")
    assert accepted["verified"]
    assert accepted["schema"] == "original-N23-B15-actual-complete-residual-types-restoration-v1"
    assert accepted["source_sha256"] == sha(ROOT / "extract_n23_actual_residual_types.py")
    assert (accepted["N"], accepted["B"]) == (23, 15)
    assert accepted["actual_full_residual_types"] > 0
    fullpath = restored / accepted["full_types_file"]
    assert fullpath.resolve().is_relative_to(restored)
    assert sha(fullpath) == accepted["full_types_sha256"]
    core = read(corepath)
    assert (core["N"], core["B"]) == (23, 15)
    candidate = sorted(sum(1 << v for v in face) for face in core["all_faces"])
    assert len(candidate) == 29
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constantspath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    frozen = {str(path): sha(path) for path in (
        Path(__file__), restored / "VERIFIED.json", fullpath, corepath, constantspath,
        ROOT / "probe_collar_batches.py", HIGH / "candidate_domain.py",
        HIGH / "exact_graph.py", HIGH / "n22_core_case.py",
        HIGH / "audit_streamed_hierarchy.py", Path(exact.kernel.__file__))}
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 23, "B": 15, "restored_full_types_sha256": sha(fullpath),
        "restoration_report_sha256": sha(restored / "VERIFIED.json"),
        "candidate_full_faces": candidate, "force_limit": args.limit,
        "all_faces_retained_not_outer_only": True, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    counts, groupcounts = Counter(), Counter()
    previous, started = -1, time.monotonic()
    with fullpath.open(encoding="ascii") as source, \
            (output / "OUTCOMES.jsonl").open("x", encoding="ascii") as ledger:
        for line in source:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            index = row["index"]
            assert type(index) is int and previous < index
            previous = index
            assert row["no_lower_bound_payment_by_extraction"]
            masks = row["faces"]
            assert masks == sorted(set(masks)) and len(masks) == 29
            mapping = full_candidate_map(masks, candidate)
            if mapping is not None:
                outcome = {
                    "index": index, "outer_group": row["outer_group"],
                    "status": "exact-candidate-full-type-retained",
                    "candidate_full_to_actual_map": mapping,
                    "nonstrict_core_theorem_payment_not_claimed_by_proposal": True,
                }
            else:
                nodes, failure = make(15, 23, masks, constants, args.limit)
                if nodes is None:
                    outcome = {"index": index, "outer_group": row["outer_group"],
                               "status": "pending", **failure}
                else:
                    result = exact.verify(15, 23, masks, nodes, constants)
                    assert result["minimum_force_margin"] is not None
                    assert F(result["minimum_force_margin"]) > 0
                    treepath = output / f"type-{index:08}.json.gz"
                    with gzip.open(treepath, "xt", encoding="utf8") as stream:
                        json.dump({
                            "N": 23, "B": 15, "full_centers": 23, "index": index,
                            "faces": masks, "nodes": nodes,
                            "restored_full_types_sha256": sha(fullpath),
                            "constants_sha256": sha(constantspath),
                            "radius_upper": constants["radius_upper"],
                        }, stream, separators=(",", ":"))
                    outcome = {"index": index, "outer_group": row["outer_group"],
                               "status": "strict", "tree_sha256": sha(treepath),
                               "exact_result": result}
            counts[outcome["status"]] += 1
            groupcounts[str(row["outer_group"])] += 1
            ledger.write(json.dumps(outcome, separators=(",", ":"))+"\n")
            ledger.flush()
            if sum(counts.values()) % 10 == 0:
                print("N23 actual full-type proposals", sum(counts.values()),
                      "/", accepted["actual_full_residual_types"], dict(counts),
                      "seconds", round(time.monotonic()-started, 1), flush=True)
    assert sum(counts.values()) == accepted["actual_full_residual_types"]
    assert dict(groupcounts) == accepted["selected_original_outer_group_members"]
    for path, expected in frozen.items():
        assert sha(path) == expected
    publish(output / "SUMMARY.json", {
        "N": 23, "B": 15, "actual_full_types_processed": sum(counts.values()),
        "counts": dict(counts), "outcomes_sha256": sha(output / "OUTCOMES.jsonl"),
        "input_bindings_sha256": sha(output / "INPUT-BINDINGS.json"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "independent_actual_type_replay_and_parent_residual_payment_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23 actual full-type proposal stage ended:", dict(counts),
          "; independent replay required", flush=True)


if __name__ == "__main__":
    main()
