"""Independent stdlib-only acceptance of a regenerated complete ear disjunction."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, bind, unchanged
from eight_rod_angles import constants_gate, verify_cycle
from zero_budget_ear_kernel import ear_branches

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proposal", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    derivation = read(ROOT / "zero-budget-ear-kernel-derivation.json")
    assert derivation["verified_mechanical_extraction"]
    original = ROOT / "probe_zero_budget_ear_covers.py"
    assert derivation["original_source_sha256"] == sha(original)
    assert derivation["derived_source_sha256"] == sha(ROOT / "zero_budget_ear_kernel.py")
    assert derivation["source_sha256"] == sha(ROOT / "derive_zero_budget_ear_kernel.py")
    source_text = original.read_text(encoding="utf8")
    assert source_text[source_text.index("def ear_branches("):source_text.index("\ndef experiment(")] == derivation["exact_function_text"]
    assert (ROOT / "zero_budget_ear_kernel.py").read_text(encoding="utf8") == derivation["preamble"]+derivation["exact_function_text"]
    branchespath, outcomespath = args.proposal / "BRANCHES.json", args.proposal / "OUTCOMES.jsonl"
    data = read(branchespath)
    N, B, centers, outer = (data[k] for k in ("N", "B", "source_collar_centers", "source_collar_faces"))
    assert N == centers == 25 and 14 <= B <= 17
    holes, branches, impossible = ear_branches(N, B, centers, outer, data["method"])
    expected = [{"id": j, "centers": N, "faces": list(faces), "added_faces": added}
                for j, (faces, added) in enumerate(sorted(branches.items()))]
    assert data["holes"] == holes and data["branches"] == expected
    assert data["topologically_impossible_branches"] == impossible
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants, consthash = read(constants_path), sha(constants_path)
    constants_gate(constants)
    files, counts = {}, Counter()
    minimum = None
    for path in (
        Path(__file__), branchespath, outcomespath, constants_path,
        ROOT / "ZERO-BUDGET-EAR-COVER-SOURCE.md", ROOT / "zero_budget_ear_kernel.py",
        ROOT / "derive_zero_budget_ear_kernel.py", ROOT / "zero-budget-ear-kernel-derivation.json",
        original, ROOT / "complete_simple_collar.py", ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md",
        ROOT / "CLOSED-BOUNDARY-FAN-TRANSFER.md", ROOT / "eight_rod_angles.py",
        HIGH / "exact_graph.py", HIGH.parent / "round2-grouped/partial_force_exact.py",
        exact.kernel.ARCS / "exact_arcs.py",
    ):
        bind(files, path)
    count = 0
    with outcomespath.open(encoding="ascii") as stream:
        for index, line in enumerate(stream):
            assert index < len(expected)
            outcome = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert outcome["branch"] == index
            branch = expected[index]
            status = outcome["status"]
            if status == "pending":
                counts["pending"] += 1
            elif status == "exact-angle-excluded":
                result = verify_cycle(B, centers, branch["faces"], outcome["cycle"], constants)
                assert result == outcome["exact_cycle_check"]
                counts["standalone_exact_angle_lower"] += 1
            else:
                assert status == "exact-tree-excluded"
                treepath = args.proposal / f"branch-{index:05}.json.gz"
                assert sha(treepath) == outcome["tree_sha256"]
                with gzip.open(treepath, "rt", encoding="utf8") as tree_stream:
                    tree = json.load(tree_stream, object_pairs_hook=no_duplicate_keys)
                assert (tree["N"], tree["B"], tree["centers"], tree["faces"]) == (
                    N, B, centers, branch["faces"])
                assert tree["constants_sha256"] == consthash
                assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in tree["nodes"])
                result = exact.verify(B, centers, branch["faces"], tree["nodes"], constants)
                assert result["verified"] and result["nodes"] == outcome["nodes"]
                assert result["counts"] == outcome["counts"]
                if result["counts"].get("DUAL", 0):
                    margin = F(result["minimum_force_margin"])
                    assert margin > 0
                    minimum = margin if minimum is None else min(minimum, margin)
                else:
                    assert result["counts"].get("EMPTY", 0) > 0
                    assert result["minimum_force_margin"] is None
                counts["standalone_exact_tree_lower"] += 1
                bind(files, treepath)
            count += 1
    assert count == len(expected) == sum(counts.values())
    unchanged(files)
    publish(args.output, {
        "verified": True, "schema": "zero-budget-ear-disjunction-exact-acceptance-v1",
        "N": N, "B": B, "collar_centers": centers, "collar_faces": outer, "holes": holes,
        "new_internal_center_budget": 0, "method": data["method"],
        "retained_necessary_branches": count, "impossible_three_face_edge_branches": len(impossible),
        "fresh_standalone_exact_payments": dict(counts), "pending_branches": counts["pending"],
        "all_full_simple_disk_completions_paid_by_ear_cover": counts["pending"] == 0,
        "scope_requires_same_N_B_and_full_simple_disk_completion": True,
        "not_a_standalone_geometric_collar_exclusion": True,
        "not_a_full_type_enumeration_or_global_N25_proof": True,
        "radius_threshold": constants["radius_upper"],
        "minimum_force_margin": None if minimum is None else str(minimum),
        "source_induction_sha256": sha(ROOT / "ZERO-BUDGET-EAR-COVER-SOURCE.md"),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("Independent ear-cover acceptance:", dict(counts),
          "; complete fixed-family lower paid:", counts["pending"] == 0, flush=True)


if __name__ == "__main__":
    main()
