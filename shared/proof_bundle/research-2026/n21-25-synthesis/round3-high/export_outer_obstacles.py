"""Exact paid n23 outer graph patterns, independent of provisional row counts."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import json
import sys
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    groupspath = ROOT / "evidence/n23-B13-paid-run0-outer-prototypes-resume1/GROUPS.json"
    receiptpath = ROOT / "evidence/n23-B13-paid-run0-outer-prototype-force-resume1/SUMMARY.json"
    replaypath = ROOT / "evidence/n23-B13-paid-run0-outer-prototype-replay-resume1.json"
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    groups, receipt, replay, constants = map(read, (groupspath, receiptpath, replaypath, constantspath))
    assert (groups["N"], groups["B"], groups["threshold"]) == (23, 13, 1)
    assert replay["verified"] and replay["exact_groups_replayed"] == 95
    assert replay["pending_groups"] == receipt["pending_groups"] == 0
    assert replay["groups_sha256"] == receipt["groups_sha256"] == sha(groupspath)
    assert replay["receipt_sha256"] == sha(receiptpath)
    assert replay["source_sha256"] == sha(ROOT / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
    assert constants["N"] == 23 and F(constants["radius_upper"]) == F("0.249953776586051")
    outcomes = receipt["outcomes"]
    assert sorted(row["group"] for row in outcomes) == list(range(95))
    args.output.mkdir(parents=True)
    files = {p.resolve().relative_to(WORK).as_posix(): sha(p) for p in (
        Path(__file__), groupspath, receiptpath, replaypath, constantspath,
        ROOT / "exact_graph.py", ROOT / "stream_catalog.py", ROOT / "replay_group_stage.py",
        ROOT.parent / "round2-grouped/partial_force_exact.py", exact.kernel.ARCS / "exact_arcs.py")}
    obstacles = []
    tablepath = args.output / "OBSTACLES.tsv"
    with tablepath.open("x", encoding="ascii", newline="\n") as stream:
        stream.write("strict-outer-obstacle-library-v1\n")
        for outcome in sorted(outcomes, key=lambda row: row["group"]):
            assert outcome["status"] == "excluded"
            group = groups["groups"][outcome["group"]]
            assert all((mask & ((1 << 13)-1)).bit_count() >= 1 for mask in group["faces"])
            path = receiptpath.parent / f"group-{group['id']:07}.json.gz"
            assert sha(path) == outcome["tree_sha256"]
            with gzip.open(path, "rt", encoding="utf8") as treefile:
                tree = json.load(treefile, object_pairs_hook=no_duplicate_keys)
            assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                23, 13, group["centers"], group["faces"])
            assert tree["groups_sha256"] == sha(groupspath)
            assert tree["constants_sha256"] == sha(constantspath)
            result = exact.verify(13, group["centers"], group["faces"], tree["nodes"], constants)
            assert result["counts"] == outcome["counts"] and result["nodes"] == outcome["nodes"]
            assert F(result["minimum_force_margin"]) > 0
            oid = len(obstacles)
            relative = path.resolve().relative_to(WORK).as_posix()
            files[relative] = outcome["tree_sha256"]
            obstacles.append({"id": oid, "B": 13, "centers": group["centers"], "faces": group["faces"],
                              "source_group": group["id"], "tree_file_relative_to_workspace": relative,
                              "tree_sha256": outcome["tree_sha256"], "fresh_exact_replay": result})
            stream.write("\t".join(map(str, [oid, 13, group["centers"],
                                            len(group["faces"]), *group["faces"]]))+"\n")
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    report = {"verified": True, "schema": "strict-outer-obstacle-library-v1",
              "source_N": 23, "threshold": 1, "radius_threshold": constants["radius_upper"],
              "obstacle_count": len(obstacles), "obstacles": obstacles, "files": files,
              "pattern_table_sha256": sha(tablepath), "source_sha256": sha(Path(__file__)),
              "all_library_trees_fresh_exact_replayed": True, "no_root_or_local_theorem_used": True,
              "no_optimizer_imported": True, "provisional_run_coverage_not_used_as_premise": True,
              "global_optimality_proved": False,
              "scope": "95 standalone whole-angle outer-graph exclusions; not a complete target family"}
    (args.output / "LIBRARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N23 outer-graph obstacle library exact PASS: 95; all targets remain separate", flush=True)


if __name__ == "__main__":
    main()
