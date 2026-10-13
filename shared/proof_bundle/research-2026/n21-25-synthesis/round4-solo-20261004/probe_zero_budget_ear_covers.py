"""Test complete ear covers on already-paid families, then probe small branches."""
from pathlib import Path
from itertools import combinations, product
from collections import Counter
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from probe_groups import make
from stream_catalog import sha, no_duplicate_keys
from group_catalog import validate
from complete_simple_collar import simple_holes, bits
from n25_outer_search import read, publish, unchanged
from eight_rod_angles import constants_gate, exclusion

assert __debug__


def ear_branches(N, B, centers, outer, method):
    assert N == centers == 25, "ear cover requires zero new internal center budget at N25"
    holes = simple_holes(centers, B, outer)
    assert holes and method in ("one-per-hole", "two-per-large-hole")
    options = []
    for cycle in holes:
        K = len(cycle)
        ears = [sum(1 << cycle[j] for j in ((i-1) % K, i, (i+1) % K)) for i in range(K)]
        if method == "one-per-hole" or K == 3:
            choices = {(ear,) for ear in ears}
        else:
            choices = {tuple(sorted((ears[i], ears[j]))) for i, j in combinations(range(K), 2)
                       if (i-j) % K not in (1, K-1)}
        assert choices
        options.append(sorted(choices))
    branches, impossible = {}, []
    for chosen in product(*options):
        added = sorted({mask for selection in chosen for mask in selection})
        faces = sorted(set(outer) | set(added))
        incidence = {}
        for mask in faces:
            for edge in combinations(bits(mask), 2):
                incidence.setdefault(edge, []).append(mask)
        bad = next(((edge, masks) for edge, masks in incidence.items() if len(masks) > 2), None)
        if bad is not None:
            edge, masks = bad
            assert len(set(masks[:3])) == 3
            impossible.append({"added_faces": added, "edge": list(edge), "three_faces": masks[:3],
                               "requires_full_simple_disk_condition": True})
        else:
            branches.setdefault(tuple(faces), added)
    return holes, branches, impossible


def experiment(catalog, closurepath, output):
    assert not output.exists()
    closure, collar, full = map(read, (closurepath, catalog / "INPUT-COLLAR.json", catalog / "GROUPS.json"))
    assert closure["verified"] and closure["pending_completions"] == 0
    assert closure["schema"] == "single-collar-strict-full-completion-closure-v1"
    assert closure["source_sha256"] == sha(ROOT / "close_strict_collar_family.py")
    unchanged(closure["files_relative_to_workspace"])
    N, B, centers, outer = (collar[key] for key in ("N", "B", "centers", "faces"))
    assert N == centers == 25 and collar["new_inner_centers"] == 0
    assert closure["collar_faces"] == outer and closure["collar_centers"] == centers
    assert full["group_count"] == closure["full_completion_types"]
    assert sha(catalog / "GROUPS.json") == read(catalog / "SUMMARY.json")["groups_sha256"]
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constants_gate(constants)
    output.mkdir()
    summaries = []
    for method in ("one-per-hole", "two-per-large-hole"):
        holes, branches, impossible = ear_branches(N, B, centers, outer, method)
        case = output / method
        case.mkdir()
        rows = [{"id": j, "centers": N, "faces": list(faces), "added_faces": added}
                for j, (faces, added) in enumerate(sorted(branches.items()))]
        publish(case / "BRANCHES.json", {
            "N": N, "B": B, "source_collar_centers": centers, "source_collar_faces": outer,
            "holes": holes, "method": method, "branches": rows,
            "topologically_impossible_branches": impossible,
            "not_a_complete_all_N25_catalog": True,
        })
        # Directly check every full type's actual source-center embedding.
        covered = 0
        with (catalog / "COLLAR-TO-COMPLETION.jsonl").open(encoding="ascii") as stream:
            for gid, line in enumerate(stream):
                transfer = json.loads(line, object_pairs_hook=no_duplicate_keys)
                assert transfer["group"] == gid
                mapping, target = transfer["map"], full["groups"][gid]["faces"]
                validate(N, B, outer, mapping, target)
                target_set = set(target)
                matching = []
                for branch in rows:
                    images = {sum(1 << mapping["centers"][v] for v in bits(mask))
                              for mask in branch["added_faces"]}
                    if images <= target_set:
                        validate(N, B, branch["faces"], mapping, target)
                        matching.append(branch["id"])
                assert matching, ("ear disjunction lost a paid full type", method, gid)
                covered += 1
        assert covered == full["group_count"]
        counts = Counter()
        with (case / "OUTCOMES.jsonl").open("x", encoding="ascii") as ledger:
            for branch in rows:
                cycle = exclusion(B, centers, branch["faces"], constants)
                if cycle is not None:
                    outcome = {"branch": branch["id"], "status": "exact-angle-excluded", **cycle}
                else:
                    nodes, diagnostic = make(B, centers, branch["faces"], constants, 1, route_weak=True)
                    if nodes is None:
                        outcome = {"branch": branch["id"], "status": "pending",
                                   "untrusted_optimizer_diagnostic": diagnostic}
                    else:
                        result = exact.verify(B, centers, branch["faces"], nodes, constants)
                        path = case / f"branch-{branch['id']:05}.json.gz"
                        with gzip.open(path, "wt", encoding="utf8") as stream:
                            json.dump({"N": N, "B": B, "centers": centers, "faces": branch["faces"],
                                       "nodes": nodes, "constants_sha256": sha(constants_path),
                                       "source_collar_sha256": sha(catalog / "INPUT-COLLAR.json")},
                                      stream, separators=(",", ":"))
                        outcome = {"branch": branch["id"], "status": "exact-tree-excluded",
                                   **result, "tree_sha256": sha(path)}
                ledger.write(json.dumps(outcome, separators=(",", ":"))+"\n")
                counts[outcome["status"]] += 1
        # A second stdlib-only process is still needed for new branch force
        # trees before using an all-paid branch cover in production.
        summary = {"method": method, "complete_paid_full_type_cover_controls": covered,
                   "retained_necessary_branches": len(rows), "impossible_three-face_edge_branches": len(impossible),
                   "outcomes": dict(counts), "ear_cover_itself_not_a_geometric_exclusion": True,
                   "new_branch_force_trees_independent_process_replay_still_required": True,
                   "new_collar_closure_not_claimed": True}
        summaries.append(summary)
        print("Ear cover control:", method, covered, "full types covered by", len(rows),
              "branches;", dict(counts), flush=True)
    try:
        ear_branches(25, B, 24, outer, "one-per-hole")
    except AssertionError as error:
        assert str(error) == "ear cover requires zero new internal center budget at N25"
    else:
        raise AssertionError("ear cover accepted a positive missing-center budget")
    publish(output / "SUMMARY.json", {
        "source_collar_sha256": sha(catalog / "INPUT-COLLAR.json"),
        "existing_closure_sha256": sha(closurepath), "full_catalog_sha256": sha(catalog / "GROUPS.json"),
        "source_induction_sha256": sha(ROOT / "ZERO-BUDGET-EAR-COVER-SOURCE.md"),
        "source_sha256": sha(Path(__file__)), "methods": summaries,
        "positive_missing_center_budget_rejected": True,
        "global_optimality_proved": False, "new_collar_closure_not_claimed": True,
    })


def main():
    ap = argparse.ArgumentParser()
    for name in ("catalog", "closure", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    experiment(args.catalog.resolve(), args.closure.resolve(), args.output.resolve())


if __name__ == "__main__":
    main()
