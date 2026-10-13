"""Accept sparse strict graph theorems, preserving all implicit boundary rods."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--replay", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    groups, receipt, replay = map(read, (args.groups, args.receipt, args.replay))
    B = groups["B"]
    assert B in (14, 15, 16, 17)
    assert (groups["N"], groups["B"], groups["threshold"]) == (25, B, 1)
    assert replay["verified"] and receipt["groups_sha256"] == replay["groups_sha256"] == sha(args.groups)
    assert replay["receipt_sha256"] == sha(args.receipt)
    assert replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert replay["pending_groups"] == receipt["pending_groups"] == 0
    assert replay["exact_groups_replayed"] == len(groups["groups"]) == groups["group_count"]
    assert len(receipt["outcomes"]) == groups["group_count"]
    byid = {row["group"]: row for row in receipt["outcomes"]}
    assert set(byid) == set(range(groups["group_count"]))
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constpath)
    assert constants["verified"] and F(constants["radius_upper"]) == F(239146311738101, 10**15)
    files = {}
    def bind(path):
        path = path.resolve()
        assert path.is_relative_to(WORK)
        files[path.relative_to(WORK).as_posix()] = sha(path)
    for path in (
        Path(__file__), args.groups, args.receipt, args.replay, constpath,
        HIGH / "exact_graph.py", HIGH / "replay_group_stage.py", HIGH / "stream_catalog.py",
        HIGH.parent / "round2-grouped/partial_force_exact.py", exact.kernel.ARCS / "exact_arcs.py",
        ROOT / "SPARSE-OUTER-OBSTACLE-TRANSPORT.md",
    ):
        bind(path)
    args.output.mkdir(parents=True)
    table = args.output / "OBSTACLES.tsv"
    obstacles = []
    with table.open("x", encoding="ascii", newline="\n") as stream:
        stream.write("strict-sparse-outer-obstacle-library-v1\n")
        for group in groups["groups"]:
            gid = group["id"]
            assert gid == len(obstacles) and byid[gid]["status"] == "excluded"
            centers, faces = group["centers"], group["faces"]
            assert B <= centers <= 25 and faces == sorted(set(faces)) and faces
            used = 0
            for mask in faces:
                assert mask.bit_count() == 3 and mask < 1 << centers
                assert (mask & ((1 << B)-1)).bit_count() >= 1
                used |= mask
            assert used | ((1 << B)-1) == (1 << centers)-1
            treepath = args.receipt.parent / f"group-{gid:07}.json.gz"
            assert sha(treepath) == byid[gid]["tree_sha256"]
            with gzip.open(treepath, "rt", encoding="utf8") as handle:
                tree = json.load(handle, object_pairs_hook=no_duplicate_keys)
            assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (25, B, centers, faces)
            assert tree["groups_sha256"] == sha(args.groups)
            assert tree["constants_sha256"] == sha(constpath)
            assert all(n["kind"] in ("EMPTY", "SPLIT", "DUAL") for n in tree["nodes"])
            result = exact.verify(B, centers, faces, tree["nodes"], constants)
            assert result["nodes"] == byid[gid]["nodes"] and result["counts"] == byid[gid]["counts"]
            assert F(result["minimum_force_margin"]) > 0
            bind(treepath)
            obstacles.append({
                "id": gid, "B": B, "centers": centers, "faces": faces,
                "tree_file_relative_to_workspace": treepath.resolve().relative_to(WORK).as_posix(),
                "tree_sha256": sha(treepath), "fresh_exact_replay": result,
                "boundary_sites_not_in_faces_still_have_both_anchor_rods": True,
            })
            stream.write("\t".join(map(str, (gid, B, centers, len(faces), *faces))) + "\n")
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    report = {
        "verified": True, "schema": "strict-sparse-outer-obstacle-library-v1",
        "source_N": 25, "B": B, "threshold": 1, "radius_threshold": constants["radius_upper"],
        "obstacle_count": len(obstacles), "obstacles": obstacles, "files": files,
        "pattern_table_sha256": sha(table), "source_sha256": sha(Path(__file__)),
        "all_library_trees_fresh_exact_replayed": True, "no_root_or_local_theorem_used": True,
        "all_B_boundary_sites_and_2B_anchor_rods_preserved": True,
        "proper_face_subset_injections_required_for_transport": True,
        "parents_samples_and_minimality_not_used_as_theorem_premises": True,
        "global_optimality_proved": False,
        "scope": "standalone strict sparse graph theorems on their own whole angle domains",
    }
    (args.output / "LIBRARY.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Sparse N25/B14 graph library fresh exact acceptance PASS:", len(obstacles), flush=True)


if __name__ == "__main__":
    main()
