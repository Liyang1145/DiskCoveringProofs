"""Freshly replay all paid n22 two-boundary-face obstacles for cross-order use.

Exports graph patterns plus precise payment references, not target proofs.
No root/local theorem or optimizer is used. Matching/injection and complete
target enumeration must still be paid separately.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import json
import sys
import time
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
EV = ROOT / "evidence"
WORK = ROOT.parents[2].resolve()
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n22.json"
    constants = read(constantspath)
    assert constants["verified"] and constants["N"] == 22
    assert F(constants["radius_upper"]) == F("0.253251459835093")
    dependencies = {p.resolve().relative_to(WORK).as_posix(): sha(p) for p in (
        constantspath, Path(__file__), ROOT / "exact_graph.py", ROOT / "stream_catalog.py",
        ROOT / "replay_group_stage.py", ROOT.parent / "round2-grouped/partial_force_exact.py",
        exact.kernel.ARCS / "exact_arcs.py")}
    obstacles = []
    totals = {}
    started = time.monotonic()
    tablepath = args.output / "OBSTACLES.tsv"
    with tablepath.open("x", encoding="ascii", newline="\n") as table:
        table.write("strict-obstacle-library-v1\n")
        for B in (13, 14, 15):
            grouppath = EV / f"n22-B{B}-pair-resume1/GROUPS.json"
            receiptpath = EV / f"n22-B{B}-pair-root-resume1/SUMMARY.json"
            replaypath = EV / f"n22-B{B}-pair-replay-resume1.json"
            groups, receipt, paid = map(read, (grouppath, receiptpath, replaypath))
            assert (groups["N"], groups["B"], groups["threshold"]) == (22, B, 2)
            assert paid["verified"] and (paid["N"], paid["B"]) == (22, B)
            assert sha(grouppath) == paid["groups_sha256"] == receipt["groups_sha256"]
            assert sha(receiptpath) == paid["receipt_sha256"]
            assert paid["source_sha256"] == sha(ROOT / "replay_group_stage.py")
            assert paid["exact_checker_sha256"] == sha(ROOT / "exact_graph.py")
            for path in (grouppath, receiptpath, replaypath):
                dependencies[path.resolve().relative_to(WORK).as_posix()] = sha(path)
            assert [g["id"] for g in groups["groups"]] == list(range(groups["group_count"]))
            outcomes = receipt["outcomes"]
            assert sorted(r["group"] for r in outcomes) == list(range(groups["group_count"]))
            count = members = 0
            seen = set()
            for outcome in sorted(outcomes, key=lambda row: row["group"]):
                assert outcome["status"] in ("excluded", "pending")
                if outcome["status"] != "excluded":
                    continue
                group = groups["groups"][outcome["group"]]
                faces = group["faces"]
                assert all((mask & ((1 << B)-1)).bit_count() >= 2 for mask in faces)
                assert tuple(faces) not in seen
                seen.add(tuple(faces))
                path = receiptpath.parent / f"group-{group['id']:07}.json.gz"
                assert sha(path) == outcome["tree_sha256"]
                with gzip.open(path, "rt", encoding="utf8") as stream:
                    tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
                assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                    22, B, group["centers"], faces)
                assert tree["groups_sha256"] == sha(grouppath)
                assert tree["constants_sha256"] == sha(constantspath)
                assert tree["radius_upper"] == constants["radius_upper"]
                result = exact.verify(B, group["centers"], faces, tree["nodes"], constants)
                assert F(result["minimum_force_margin"]) > 0
                assert result["nodes"] == outcome["nodes"] and result["counts"] == outcome["counts"]
                oid = len(obstacles)
                relative = path.resolve().relative_to(WORK).as_posix()
                dependencies[relative] = outcome["tree_sha256"]
                obstacles.append({"id": oid, "B": B, "centers": group["centers"],
                                  "faces": faces, "source_group": group["id"],
                                  "tree_file_relative_to_workspace": relative,
                                  "tree_sha256": outcome["tree_sha256"],
                                  "fresh_exact_replay": result})
                table.write("\t".join(map(str, [oid, B, group["centers"], len(faces), *faces]))+"\n")
                count += 1
                members += group["members"]
                if len(obstacles) % 500 == 0:
                    print("Portable strict graph obstacles freshly replayed", len(obstacles),
                          "seconds", round(time.monotonic()-started, 1), flush=True)
            assert count == paid["exact_groups_replayed"]
            assert members == paid["associated_member_count"]
            totals[str(B)] = count
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    report = {"verified": True, "schema": "strict-obstacle-library-v1",
              "obstacle_count": len(obstacles), "counts_by_boundary": totals,
              "radius_threshold": constants["radius_upper"],
              "pattern_table_sha256": sha(tablepath), "obstacles": obstacles,
              "files": dependencies, "all_library_trees_fresh_exact_replayed": True,
              "no_root_or_local_theorem_used": True, "no_optimizer_imported": True,
              "target_matching_or_enumeration_paid_here": False,
              "global_optimality_proved": False,
              "scope": "portable complete-angle strict graph exclusions only",
              "source_sha256": sha(Path(__file__))}
    (args.output / "LIBRARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Portable strict obstacle library exact PASS:", len(obstacles),
          "patterns;", totals, "; target completeness still unpaid", flush=True)


if __name__ == "__main__":
    main()
