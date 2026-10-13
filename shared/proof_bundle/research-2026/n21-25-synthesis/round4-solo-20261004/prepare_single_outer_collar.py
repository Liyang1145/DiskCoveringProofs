"""Promote one observed weak collar to a fixed-order completion obligation.

The source may have fewer total centers; the output never claims a complete
n25 boundary family. It retains the exact same outer faces and labels.
"""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical, validate
from n25_outer_search import read, publish
from complete_simple_collar import simple_holes

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--index", type=int, default=0)
    ap.add_argument("--target-n", type=int, default=25)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    header, controls = map(read, (args.catalog, args.controls))
    assert header["schema"] == "outer-collar-overapproximation-v1"
    assert header["complete_necessary_outer_search"] and not header["complete_full_triangulations"]
    assert controls["verified"] and controls["schema"] == "eight-rod-sparse-complete-partition-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_eight_sparse_guard.py")
    B = header["B"]
    assert B in (14, 15, 16, 17) and header["N"] <= args.target_n == 25
    assert controls["B"] == B
    assert any(row["N"] == header["N"] and row["B"] == B and row["mode"] == header["mode"]
               and row["residual_sha256"] == sha(args.catalog) for row in controls["cases"])
    assert 0 <= args.index < len(header["weak_graphs"])
    row = header["weak_graphs"][args.index]
    centers, faces = row["centers"], row["faces"]
    assert B <= centers <= args.target_n
    code, source_map = canonical(centers, B, faces, 1)
    assert list(code) == faces and len(source_map["centers"]) == centers
    holes = simple_holes(centers, B, faces)
    identity = {"centers": list(range(centers)), "anchors": list(range(B)),
                "orientation": 1, "shift": 0}
    validate(centers, B, faces, identity, faces)
    output.mkdir()
    bindings = output / "bindings.jsonl"
    bindings.write_text(json.dumps({"index": 0, "group": 0, "map": identity},
                                   separators=(",", ":"))+"\n", encoding="utf8")
    publish(output / "GROUPS.json", {
        "N": args.target_n, "B": B, "threshold": 1,
        "groups": [{"id": 0, "centers": centers, "faces": faces, "members": 1}],
        "group_count": 1, "selected_types": 1, "catalog_types": 1,
        "catalog_sha256": sha(args.catalog), "bindings_file": bindings.name,
        "bindings_sha256": sha(bindings), "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": False, "parent_groups_sha256": None,
        "parent_proof_sha256": None, "one_fixed_outer_collar_only": True,
        "not_a_complete_boundary_family": True, "global_optimality_proved": False,
        "source_sha256": sha(Path(__file__)),
    })
    publish(output / "SOURCE.json", {
        "source_catalog_sha256": sha(args.catalog), "source_controls_sha256": sha(args.controls),
        "source_total_order": header["N"], "target_completion_order": args.target_n,
        "source_index": args.index, "B": B, "collar_centers": centers,
        "holes": holes, "additional_internal_center_budget": args.target_n-centers,
        "not_an_unconditional_n25_family": True, "global_optimality_proved": False,
    })
    print("Single B", B, "outer collar completion obligation prepared:",
          centers, "used centers;", args.target_n-centers, "new inner centers;",
          [len(hole) for hole in holes], "hole sizes", flush=True)


if __name__ == "__main__":
    main()
