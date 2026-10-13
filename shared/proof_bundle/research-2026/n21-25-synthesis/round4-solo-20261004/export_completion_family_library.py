"""Accept paid fixed-order collar completion families, never geometric weak-graph exclusions."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from complete_simple_collar import simple_holes
from n25_outer_search import read, bind, unchanged, publish

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--closure", type=Path, action="append", required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 25
    U = F(constants["radius_upper"])
    assert U == F(239146311738101, 10**15)
    alpha = F(3, 2)*(1-U*U)
    assert 0 < alpha and alpha*alpha < 2
    files, patterns = {}, []
    seen = set()
    for closurepath in args.closure:
        closure = read(closurepath)
        assert closure["verified"] and closure["N"] == 25
        assert closure["complete_this_simple_hole_completion_family"]
        assert closure["pending_completions"] == 0 and closure["global_optimality_proved"] is False
        B, centers, faces = closure["B"], closure["collar_centers"], closure["collar_faces"]
        assert B in (14, 15, 16, 17) and B <= centers <= 25
        holes = simple_holes(centers, B, faces)
        assert holes, "this fixed-order library only handles collars with paid inner completions"
        if closure["schema"] == "single-collar-strict-full-completion-closure-v1":
            assert closure["source_sha256"] == sha(ROOT / "close_strict_collar_family.py")
            assert closure["radius_threshold"] == str(U)
            assert closure["strictly_excluded"] == closure["full_completion_types"] > 0
            assert closure["known_attaining_core_lower_paid"] == 0
            assert closure["every_full_disk_and_exact_outer_face_map_rechecked"]
            mode = "no_full_simple_disk_realization_with_all_rods_at_most_U25"
        else:
            assert closure["schema"] == "single-n25-candidate-collar-completion-closure-v1"
            assert closure["source_sha256"] == sha(ROOT / "close_candidate_collar.py")
            assert closure["core_lower_radius"] == "1/(sqrt(6)+sqrt(3))"
            assert closure["strictly_excluded"]+closure["known_attaining_core_lower_paid"] == closure["full_completion_types"] == 91
            assert closure["known_attaining_core_lower_paid"] == 1 and closure["B"] == 16
            mode = "no_full_simple_disk_realization_with_all_rods_strictly_below_exact_rstar"
        assert closure["simple_hole_source_induction_sha256"] == sha(ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md")
        unchanged(closure["files_relative_to_workspace"])
        files.update(closure["files_relative_to_workspace"])
        bind(files, closurepath)
        key = (B, centers, tuple(faces))
        assert key not in seen
        seen.add(key)
        patterns.append({
            "id": len(patterns), "full_order": 25, "B": B, "centers": centers, "faces": faces,
            "holes": holes, "new_internal_center_budget": 25-centers,
            "lower_mode": mode, "full_completion_types_paid": closure["full_completion_types"],
            "strictly_excluded_full_types": closure["strictly_excluded"],
            "exact_core_lower_full_types": closure["known_attaining_core_lower_paid"],
            "closure_file_relative_to_library": str(closurepath.resolve().relative_to(ROOT)),
            "closure_sha256": sha(closurepath),
            "complete_boundary_fans_checked": True,
            "not_a_standalone_geometric_weak_graph_exclusion": True,
        })
    for path in (Path(__file__), constants_path, ROOT / "complete_simple_collar.py",
                 ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md",
                 ROOT / "CLOSED-BOUNDARY-FAN-TRANSFER.md"):
        bind(files, path)
    unchanged(files)
    output.mkdir()
    table = output / "COMPLETION-PATTERNS.tsv"
    with table.open("x", encoding="ascii", newline="\n") as stream:
        stream.write("paid-simple-collar-completion-library-v1\n")
        for pattern in patterns:
            stream.write("\t".join(map(str, [pattern["id"], pattern["B"], pattern["centers"],
                                            len(pattern["faces"]), *pattern["faces"]]))+"\n")
    publish(output / "LIBRARY.json", {
        "verified": True, "schema": "paid-simple-collar-completion-library-v1",
        "full_order": 25, "patterns": patterns, "pattern_count": len(patterns),
        "radius_lower_object": "1/(sqrt(6)+sqrt(3))",
        "search_predicate": "exclude strictly improving covers; not every weak-graph U25 realization",
        "exact_N_and_B_required": True, "full_simple_disk_completion_required": True,
        "all_source_boundary_fans_saturated": True,
        "source_completed_family_bindings_checked": True,
        "source_sha256": sha(Path(__file__)), "table_sha256": sha(table),
        "files_relative_to_workspace": files,
        "boundary_fan_transport_source_sha256": sha(ROOT / "CLOSED-BOUNDARY-FAN-TRANSFER.md"),
        "global_optimality_proved": False,
    })
    print("Paid completion-family library accepted:", len(patterns),
          "closed boundary fans; topology-conditioned lower bounds only", flush=True)


if __name__ == "__main__":
    main()
