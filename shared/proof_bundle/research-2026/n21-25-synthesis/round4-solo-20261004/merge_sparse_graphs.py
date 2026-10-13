"""Freshly normalize a union of standalone strict libraries, not family coverage."""
from pathlib import Path
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha
from run_sparse_collar import sparse_library_gate
from n25_outer_search import unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, action="append", required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert len(args.library) >= 2
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    merged, dependencies, inputs = {}, {}, []
    for librarypath in args.library:
        constants, library, _, files = sparse_library_gate(librarypath.resolve())
        dependencies.update(files)
        inputs.append({"library": librarypath.resolve().relative_to(WORK).as_posix(),
                       "sha256": sha(librarypath)})
        for obstacle in library["obstacles"]:
            treepath = WORK / obstacle["tree_file_relative_to_workspace"]
            with gzip.open(treepath, "rt", encoding="utf8") as stream:
                tree = json.load(stream)
            theorem = exact.verify(14, obstacle["centers"], obstacle["faces"],
                                   tree["nodes"], constants)
            assert theorem == obstacle["fresh_exact_replay"]
            merged.setdefault(tuple(obstacle["faces"]), (obstacle["centers"], tree["nodes"], theorem))
    output.mkdir()
    manifest = output / "SOURCE-LIBRARIES.json"
    manifest.write_text(json.dumps({"libraries": inputs, "source_file_bindings": dependencies,
                                    "standalone_strict_graphs_only": True}, indent=2)+"\n",
                        encoding="utf8")
    groups = []
    bindings = output / "bindings.jsonl"
    with bindings.open("x", encoding="utf8") as stream:
        for code, (centers, nodes, theorem) in merged.items():
            gid = len(groups)
            groups.append({"id": gid, "centers": centers, "faces": list(code), "members": 1})
            stream.write(json.dumps({
                "index": gid, "group": gid,
                "map": {"centers": list(range(centers)), "anchors": list(range(14)),
                        "orientation": 1, "shift": 0},
            }, separators=(",", ":"))+"\n")
    group_path = output / "GROUPS.json"
    group_path.write_text(json.dumps({
        "N": 25, "B": 14, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups),
        "catalog_sha256": sha(manifest), "bindings_file": bindings.name,
        "bindings_sha256": sha(bindings), "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": False, "parent_groups_sha256": None,
        "parent_proof_sha256": None, "members_are_standalone_graphs_not_cover_types": True,
        "not_a_complete_family": True, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    outcomes = []
    for group in groups:
        _, nodes, theorem = merged[tuple(group["faces"])]
        treepath = output / f"group-{group['id']:07}.json.gz"
        with gzip.open(treepath, "xt", encoding="utf8") as stream:
            json.dump({
                "N": 25, "B": 14, "partial_centers": group["centers"], "faces": group["faces"],
                "nodes": nodes, "groups_sha256": sha(group_path),
                "constants_sha256": sha(constpath), "radius_upper": constants["radius_upper"],
            }, stream, separators=(",", ":"))
        outcomes.append({"group": group["id"], "status": "excluded", **theorem,
                         "members": 1, "tree_sha256": sha(treepath)})
    unchanged(dependencies)
    (output / "SUMMARY.json").write_text(json.dumps({
        "N": 25, "B": 14, "groups_sha256": sha(group_path), "outcomes": outcomes,
        "excluded_groups": len(groups), "pending_groups": 0,
        "catalog_members_excluded": len(groups), "requested_groups_complete": True,
        "source_sha256": sha(Path(__file__)), "source_libraries_sha256": sha(manifest),
        "whole_catalog_exclusion_proved": False, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("Standalone strict library union normalized:", len(groups), "graphs", flush=True)


if __name__ == "__main__":
    main()
