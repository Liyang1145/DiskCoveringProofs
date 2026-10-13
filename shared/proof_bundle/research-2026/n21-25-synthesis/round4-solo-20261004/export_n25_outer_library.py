"""Reprove and export only standalone strict n25/B14 whole-angle obstacles.

Discovery sample membership/counts never enter the graph theorem. No LOCAL
or numerical leaf is accepted. All exported trees are replayed from integers.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2]
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def export(groupspath, receiptpath, replaypath, output):
    assert not output.exists()
    groups, receipt, replay = map(read, (groupspath, receiptpath, replaypath))
    assert (groups["N"], groups["B"], groups["threshold"]) == (25, 14, 1)
    assert receipt["groups_sha256"] == replay["groups_sha256"] == sha(groupspath)
    assert replay["verified"] and replay["receipt_sha256"] == sha(receiptpath)
    assert replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert replay["exact_groups_replayed"] == receipt["excluded_groups"] > 0
    assert len(receipt["outcomes"]) == groups["group_count"] == len(groups["groups"])
    assert sorted(r["group"] for r in receipt["outcomes"]) == list(range(groups["group_count"]))
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constantspath)
    assert constants["verified"] and constants["N"] == 25
    assert F(constants["radius_upper"]) == F(239146311738101, 10**15)
    files = {}
    def bind(path):
        path = path.resolve()
        assert path.is_relative_to(WORK.resolve())
        files[path.relative_to(WORK.resolve()).as_posix()] = sha(path)
    for path in (Path(__file__), groupspath, receiptpath, replaypath, constantspath,
                 HIGH / "exact_graph.py", HIGH / "replay_group_stage.py",
                 HIGH / "stream_catalog.py", HIGH.parent / "round2-grouped/partial_force_exact.py",
                 exact.kernel.ARCS / "exact_arcs.py", ROOT / "N25-OUTER-OBSTACLE-TRANSPORT.md"):
        bind(path)
    output.mkdir(parents=True)
    table = output / "OBSTACLES.tsv"
    obstacles = []
    with table.open("x", encoding="ascii", newline="\n") as stream:
        stream.write("strict-outer-obstacle-library-v1\n")
        for outcome in sorted(receipt["outcomes"], key=lambda r: r["group"]):
            assert outcome["status"] in ("excluded", "pending")
            if outcome["status"] == "pending":
                continue
            group = groups["groups"][outcome["group"]]
            assert group["faces"] == sorted(set(group["faces"]))
            assert all((mask & ((1 << 14)-1)).bit_count() >= 1 for mask in group["faces"])
            used = 0
            for mask in group["faces"]:
                used |= mask
            assert used == (1 << group["centers"])-1 and 14 <= group["centers"] <= 25
            treepath = receiptpath.parent / f"group-{group['id']:07}.json.gz"
            assert sha(treepath) == outcome["tree_sha256"]
            with gzip.open(treepath, "rt", encoding="utf8") as handle:
                tree = json.load(handle, object_pairs_hook=no_duplicate_keys)
            assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                25, 14, group["centers"], group["faces"])
            assert tree["groups_sha256"] == sha(groupspath)
            assert tree["constants_sha256"] == sha(constantspath)
            assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in tree["nodes"])
            report = exact.verify(14, group["centers"], group["faces"], tree["nodes"], constants)
            assert report["counts"] == outcome["counts"] and report["nodes"] == outcome["nodes"]
            assert F(report["minimum_force_margin"]) > 0
            bind(treepath)
            oid = len(obstacles)
            obstacles.append({
                "id": oid, "B": 14, "centers": group["centers"], "faces": group["faces"],
                "source_group": group["id"],
                "tree_file_relative_to_workspace": treepath.resolve().relative_to(WORK.resolve()).as_posix(),
                "tree_sha256": sha(treepath), "fresh_exact_replay": report,
            })
            stream.write("\t".join(map(str, (oid, 14, group["centers"], len(group["faces"]), *group["faces"]))) + "\n")
    assert len(obstacles) == replay["exact_groups_replayed"]
    assert not any(n in sys.modules for n in ("numpy", "scipy", "clarabel", "mpmath"))
    result = {
        "verified": True, "schema": "strict-outer-obstacle-library-v1",
        "source_N": 25, "threshold": 1, "radius_threshold": constants["radius_upper"],
        "obstacle_count": len(obstacles), "obstacles": obstacles, "files": files,
        "pattern_table_sha256": sha(table), "source_sha256": sha(Path(__file__)),
        "all_library_trees_fresh_exact_replayed": True, "no_root_or_local_theorem_used": True,
        "no_optimizer_imported": True, "sample_or_run_completion_not_used_as_premise": True,
        "pending_source_groups_not_exported": replay["pending_groups"],
        "global_optimality_proved": False,
        "scope": "standalone same-B14 strict graph obstacles at U25; no full-family or whole-cover conclusion",
    }
    (output / "LIBRARY.json").write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N25/B14 fresh strict outer obstacle library PASS:", len(obstacles), flush=True)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--replay", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    export(args.groups, args.receipt, args.replay, args.output)


if __name__ == "__main__":
    main()
