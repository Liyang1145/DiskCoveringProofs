"""Normalize independent strict sparse libraries with the same B, offline only."""
from pathlib import Path
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha
from family_sparse_gate import sparse_library_gate
from n25_outer_search import publish, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, action="append", required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists() and len(args.library) >= 2
    merged, dependencies, inputs, B = {}, {}, [], None
    for path in args.library:
        path = path.resolve()
        assert path.is_relative_to(ROOT)
        constants, library, table, files = sparse_library_gate(path)
        if B is None:
            B = library["B"]
        assert B == library["B"]
        dependencies.update(files)
        inputs.append({"library_relative_to_round4": path.relative_to(ROOT).as_posix(),
                       "sha256": sha(path), "obstacles": library["obstacle_count"]})
        for obstacle in library["obstacles"]:
            treepath = ROOT.parents[2] / obstacle["tree_file_relative_to_workspace"]
            with gzip.open(treepath, "rt", encoding="utf8") as stream:
                tree = json.load(stream)
            report = exact.verify(B, obstacle["centers"], obstacle["faces"], tree["nodes"], constants)
            assert report == obstacle["fresh_exact_replay"]
            code = tuple(obstacle["faces"])
            if code in merged:
                assert merged[code][0] == obstacle["centers"]
            merged.setdefault(code, (obstacle["centers"], tree["nodes"], report))
    output.mkdir()
    sourcepath = output / "SOURCE-LIBRARIES.json"
    publish(sourcepath, {"libraries": inputs, "source_file_bindings": dependencies,
                         "standalone_strict_graphs_only": True})
    groups = [{"id": index, "centers": value[0], "faces": list(code), "members": 1}
              for index, (code, value) in enumerate(merged.items())]
    bindings = output / "bindings.jsonl"
    with bindings.open("x", encoding="ascii") as stream:
        for group in groups:
            stream.write(json.dumps({
                "index": group["id"], "group": group["id"],
                "map": {"centers": list(range(group["centers"])), "anchors": list(range(B)),
                        "orientation": 1, "shift": 0},
            }, separators=(",", ":"))+"\n")
    group_path = output / "GROUPS.json"
    publish(group_path, {
        "N": 25, "B": B, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups), "catalog_sha256": sha(sourcepath),
        "bindings_file": bindings.name, "bindings_sha256": sha(bindings),
        "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": False,
        "members_are_standalone_graphs_not_cover_types": True, "not_a_complete_family": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    outcomes = []
    for group in groups:
        centers, nodes, report = merged[tuple(group["faces"])]
        treepath = output / f"group-{group['id']:07}.json.gz"
        with gzip.open(treepath, "xt", encoding="utf8") as stream:
            json.dump({
                "N": 25, "B": B, "partial_centers": centers, "faces": group["faces"],
                "nodes": nodes, "groups_sha256": sha(group_path),
                "constants_sha256": sha(constants_path), "radius_upper": constants["radius_upper"],
            }, stream, separators=(",", ":"))
        outcomes.append({"group": group["id"], "status": "excluded", **report,
                         "members": 1, "tree_sha256": sha(treepath)})
    unchanged(dependencies)
    publish(output / "SUMMARY.json", {
        "N": 25, "B": B, "groups_sha256": sha(group_path), "outcomes": outcomes,
        "excluded_groups": len(groups), "pending_groups": 0,
        "catalog_members_excluded": len(groups), "requested_groups_complete": True,
        "source_sha256": sha(Path(__file__)), "source_libraries_sha256": sha(sourcepath),
        "whole_catalog_exclusion_proved": False, "global_optimality_proved": False,
    })
    print("Offline same-B strict-library union normalized:", len(groups), "graphs", flush=True)


if __name__ == "__main__":
    main()
