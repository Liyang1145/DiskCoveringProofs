"""Discover smaller strict graph obstructions by deleting face constraints.

Each retained deletion is re-proved on its own entire necessary angle domain.
Greedy reduction is not a global-minimality claim. Boundary sites remain in
the graph through their two anchor rods even if they occur in no face.
"""
from pathlib import Path
from collections import Counter
import argparse
import gzip
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from candidate_domain import configure
from group_catalog import canonical, validate
from stream_catalog import sha

assert __debug__


def prove(code, centers, constants):
    faces, edges, vertices, solver = configure(14, centers, list(code), constants)
    matrix = exact.kernel.angle_bounds(14, centers, faces, constants)
    lo, hi = exact.rootbox(matrix, constants["angle_scale"])
    box = exact.kernel.tighten(matrix, lo, hi, constants["angle_scale"])
    assert box is not None
    lo, hi = box
    force, _, _ = solver.solve_slsqp(lo, hi)
    if force is None:
        return None
    nodes = [{"kind": "DUAL", "certificate": force}]
    report = exact.verify(14, centers, list(code), nodes, constants)
    assert report["verified"]
    return nodes, report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--count", type=int, default=100)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    library = json.loads(args.library.read_text())
    assert library["verified"] and library["source_N"] == 25 and library["threshold"] == 1
    source = library["obstacles"][:args.count]
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = json.loads(constpath.read_text())
    assert constants["verified"] and constants["N"] == 25
    args.output.mkdir(parents=True)
    codes, counts, proof_by_code, parents = {}, Counter(), {}, []
    proposals = 0
    before_faces = after_faces = 0
    started = time.monotonic()
    with (args.output / "parent-maps.jsonl").open("x", encoding="utf8") as ledger:
        for index, parent in enumerate(source):
            remaining = list(parent["faces"])
            # Test a complete root theorem, never reuse the parent certificate
            # for a graph with fewer constraints / a wider angle domain.
            current_code, current_map = canonical(parent["centers"], 14, remaining, 1)
            current = prove(current_code, len(current_map["centers"]), constants)
            assert current is not None
            before_faces += len(remaining)
            order = sorted(remaining, key=lambda m: ((m & ((1 << 14)-1)).bit_count(), m))
            for remove in order:
                trial = [m for m in remaining if m != remove]
                if not trial:
                    continue
                code, mapping = canonical(parent["centers"], 14, trial, 1)
                candidate = prove(code, len(mapping["centers"]), constants)
                proposals += 1
                if candidate is not None:
                    remaining = trial
                    current_code, current_map, current = code, mapping, candidate
            centers = len(current_map["centers"])
            # The old hierarchy check_map requires equality with ALL outer
            # faces. This new reduction deliberately needs proper containment.
            # Frozen validate checks every center, anchor rod and image face.
            validate(parent["centers"], 14, current_code, current_map, parent["faces"])
            after_faces += len(current_code)
            gid = codes.setdefault(current_code, len(codes))
            counts[gid] += 1
            proof_by_code.setdefault(current_code, (centers, current))
            entry = {
                "index": index, "group": gid, "parent_obstacle": parent["id"],
                "parent_centers": parent["centers"], "parent_faces": parent["faces"],
                "remaining_faces_in_parent_labels": remaining, "map": current_map,
                "all_deletions_were_fresh_whole_root_theorems": True,
            }
            parents.append(entry)
            ledger.write(json.dumps(entry, separators=(",", ":")) + "\n")
            if (index + 1) % 20 == 0:
                ledger.flush()
                print("Sparse N25 obstacles", index + 1, "parents ->", len(codes),
                      "graphs; faces", before_faces, "->", after_faces,
                      "seconds", round(time.monotonic()-started, 1), flush=True)
    groups = [None] * len(codes)
    for code, gid in codes.items():
        centers, _ = proof_by_code[code]
        groups[gid] = {"id": gid, "centers": centers, "faces": list(code), "members": counts[gid]}
    bindingpath = args.output / "bindings.jsonl"
    with bindingpath.open("x", encoding="utf8") as stream:
        for entry in parents:
            stream.write(json.dumps({"index": entry["index"], "group": entry["group"], "map": entry["map"]},
                                    separators=(",", ":")) + "\n")
    groupspath = args.output / "GROUPS.json"
    groupspath.write_text(json.dumps({
        "N": 25, "B": 14, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(parents), "catalog_types": len(parents),
        "catalog_sha256": sha(args.library), "bindings_file": bindingpath.name,
        "bindings_sha256": sha(bindingpath), "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": False, "parent_groups_sha256": None,
        "parent_proof_sha256": None, "source_sha256": sha(Path(__file__)),
        "members_are_parent_graphs_not_actual_cover_types": True,
        "boundary_vertices_may_be_unused_in_faces_but_keep_anchor_rods": True,
        "not_a_complete_family": True, "global_optimality_proved": False,
    }, indent=2), encoding="utf8")
    outcomes = []
    for group in groups:
        nodes, report = proof_by_code[tuple(group["faces"])][1]
        path = args.output / f"group-{group['id']:07}.json.gz"
        with gzip.open(path, "wt", encoding="utf8") as stream:
            json.dump({
                "N": 25, "B": 14, "partial_centers": group["centers"], "faces": group["faces"],
                "nodes": nodes, "groups_sha256": sha(groupspath), "constants_sha256": sha(constpath),
                "radius_upper": constants["radius_upper"],
            }, stream, separators=(",", ":"))
        outcomes.append({
            "group": group["id"], "status": "excluded", **report, "members": group["members"],
            "tree_sha256": sha(path),
        })
    (args.output / "SUMMARY.json").write_text(json.dumps({
        "N": 25, "B": 14, "groups_sha256": sha(groupspath), "outcomes": outcomes,
        "excluded_groups": len(outcomes), "pending_groups": 0, "catalog_members_excluded": len(parents),
        "requested_groups_complete": True, "global_optimality_proved": False,
        "source_sha256": sha(Path(__file__)), "parent_library_sha256": sha(args.library),
        "parent_face_count": before_faces, "reduced_face_count": after_faces,
        "deletion_proposals": proposals, "global_face_minimality_not_claimed": True,
    }, indent=2), encoding="utf8")
    print("Sparse obstacle proposals complete:", len(parents), "parents ->", len(groups),
          "strict graphs; faces", before_faces, "->", after_faces, flush=True)


if __name__ == "__main__":
    main()
