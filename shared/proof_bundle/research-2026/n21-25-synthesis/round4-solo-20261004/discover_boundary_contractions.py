"""Adjacent boundary contraction is ONLY candidate generation, not theorem transfer.

Target graphs are independently re-proved on their own complete angle domains.
Any contraction producing a non-triple face is discarded. Source certificates
are never used to accept a changed-B graph.
"""
from pathlib import Path
from collections import Counter
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical, validate
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate

assert __debug__


def contract(B, centers, faces, edge):
    assert 14 < B <= 17 and B <= centers <= 25 and 0 <= edge < B
    # Rotate the chosen adjacent pair to labels B-2,B-1, then identify them.
    shift = (edge-(B-2)) % B
    old_to_new = {}
    for new in range(B):
        old = (shift+new) % B
        old_to_new[old] = min(new, B-2)
    for old in range(B, centers):
        old_to_new[old] = old-1
    masks = []
    for mask in faces:
        image = sum(1 << v for v in {old_to_new[old] for old in range(centers) if mask >> old & 1})
        if image.bit_count() != 3:
            return None
        masks.append(image)
    masks = sorted(set(masks))
    code, mapping = canonical(centers-1, B-1, masks, 1)
    assert len(mapping["centers"]) == centers-1
    validate(centers-1, B-1, code, mapping, masks)
    return len(mapping["centers"]), list(code), old_to_new


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--target-B", type=int, choices=(15, 16), required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.library, args.output = args.library.resolve(), args.output.resolve()
    assert args.library.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists()
    constants, library, table, files = sparse_library_gate(args.library)
    assert args.target_B < library["B"] <= 17
    current = {}
    for source in library["obstacles"]:
        key = (source["centers"], tuple(source["faces"]))
        current[key] = {"centers": source["centers"], "faces": source["faces"],
                        "source_obstacles": {source["id"]}, "one_generation_history": []}
    counts = []
    for B in range(library["B"], args.target_B, -1):
        new, rejected, attempts = {}, 0, 0
        for row in current.values():
            for edge in range(B):
                attempts += 1
                candidate = contract(B, row["centers"], row["faces"], edge)
                if candidate is None:
                    rejected += 1
                    continue
                centers, faces, labeling = candidate
                key = (centers, tuple(faces))
                if key not in new:
                    new[key] = {
                        "centers": centers, "faces": faces,
                        "source_obstacles": set(row["source_obstacles"]),
                        "one_generation_history": row["one_generation_history"]+[{
                            "source_B": B, "source_centers": row["centers"], "source_faces": row["faces"],
                            "adjacent_edge": edge,
                            "old_to_new_center_labels": [labeling[j] for j in range(row["centers"])],
                            "not_a_proof_transport": True,
                        }],
                    }
                else:
                    new[key]["source_obstacles"].update(row["source_obstacles"])
        current = new
        counts.append({"source_B": B, "target_B": B-1, "attempts": attempts,
                       "non_triple_candidates_discarded": rejected, "distinct_candidates": len(current)})
        assert current
    ordered = sorted(current.values(), key=lambda row: (row["faces"], row["centers"]))
    for path in (Path(__file__), args.library, ROOT / "family_sparse_gate.py", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    publish(args.output, {
        "schema": "incomplete-collar-discovery-v1", "N": 25, "B": args.target_B,
        "weak_graph_count": len(ordered),
        "weak_graphs": [{"centers": row["centers"], "faces": row["faces"]} for row in ordered],
        "candidate_provenance": [{"source_obstacles": sorted(row["source_obstacles"]),
                                 "one_generation_history": row["one_generation_history"]} for row in ordered],
        "generation_steps": counts, "source_library_sha256": sha(args.library),
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "source_theorems_not_reused_to_accept_changed_B_candidates": True,
        "all_target_graphs_require_fresh_own_complete_angle_domain_proofs": True,
        "complete_necessary_outer_search": False, "complete_family_coverage": False,
        "global_optimality_proved": False,
    })
    print("Changed-B candidates generated only:", library["B"], "->", args.target_B,
          len(ordered), "canonical graphs; no changed-B theorem accepted", flush=True)


if __name__ == "__main__":
    main()
