"""Stdlib-only acceptance and explicit transport for completed N25 collar families."""
from pathlib import Path
from fractions import Fraction as F
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate
from complete_simple_collar import simple_holes
from n25_outer_search import read, bind, unchanged

assert __debug__


def library_gate(path):
    library = read(path)
    assert library["verified"] and library["schema"] == "paid-simple-collar-completion-library-v1"
    assert library["source_sha256"] == sha(ROOT / "export_completion_family_library.py")
    assert library["full_order"] == 25 and library["exact_N_and_B_required"]
    assert library["full_simple_disk_completion_required"] and library["all_source_boundary_fans_saturated"]
    assert library["radius_lower_object"] == "1/(sqrt(6)+sqrt(3))"
    assert library["pattern_count"] == len(library["patterns"]) > 0
    files = dict(library["files_relative_to_workspace"])
    unchanged(files)
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    U = F(constants["radius_upper"])
    assert constants["verified"] and constants["N"] == 25 and U == F(239146311738101, 10**15)
    alpha = F(3, 2)*(1-U*U)
    assert 0 < alpha and alpha*alpha < 2
    table = path.parent / "COMPLETION-PATTERNS.tsv"
    assert sha(table) == library["table_sha256"]
    lines = table.read_text(encoding="ascii").splitlines()
    assert lines[0] == library["schema"] and len(lines) == library["pattern_count"]+1
    for index, pattern in enumerate(library["patterns"]):
        assert pattern["id"] == index and pattern["full_order"] == 25
        B, centers, faces = pattern["B"], pattern["centers"], pattern["faces"]
        assert simple_holes(centers, B, faces) == pattern["holes"]
        assert pattern["new_internal_center_budget"] == 25-centers
        assert pattern["complete_boundary_fans_checked"]
        assert pattern["not_a_standalone_geometric_weak_graph_exclusion"]
        assert list(map(int, lines[index+1].split())) == [index, B, centers, len(faces), *faces]
        closurepath = ROOT / pattern["closure_file_relative_to_library"]
        assert sha(closurepath) == pattern["closure_sha256"]
        closure = read(closurepath)
        assert closure["verified"] and closure["N"] == 25 and closure["B"] == B
        assert closure["collar_centers"] == centers and closure["collar_faces"] == faces
        assert closure["pending_completions"] == 0
        assert closure["complete_this_simple_hole_completion_family"]
        assert pattern["full_completion_types_paid"] == closure["full_completion_types"]
        assert pattern["strictly_excluded_full_types"] == closure["strictly_excluded"]
        assert pattern["exact_core_lower_full_types"] == closure["known_attaining_core_lower_paid"]
        if pattern["lower_mode"] == "no_full_simple_disk_realization_with_all_rods_at_most_U25":
            assert closure["schema"] == "single-collar-strict-full-completion-closure-v1"
            assert closure["source_sha256"] == sha(ROOT / "close_strict_collar_family.py")
            assert closure["radius_threshold"] == str(U) and closure["known_attaining_core_lower_paid"] == 0
            assert closure["strictly_excluded"] == closure["full_completion_types"]
        else:
            assert pattern["lower_mode"] == "no_full_simple_disk_realization_with_all_rods_strictly_below_exact_rstar"
            assert closure["schema"] == "single-n25-candidate-collar-completion-closure-v1"
            assert closure["source_sha256"] == sha(ROOT / "close_candidate_collar.py")
            assert closure["core_lower_radius"] == library["radius_lower_object"]
            assert closure["strictly_excluded"]+closure["known_attaining_core_lower_paid"] == closure["full_completion_types"]
        unchanged(closure["files_relative_to_workspace"])
    assert library["boundary_fan_transport_source_sha256"] == sha(ROOT / "CLOSED-BOUNDARY-FAN-TRANSFER.md")
    for p in (path, table, Path(__file__), ROOT / "CLOSED-BOUNDARY-FAN-TRANSFER.md"):
        bind(files, p)
    return library, table, files


def validate_outer_payment(pattern, target_n, target_B, target_faces, mapping):
    assert target_n == pattern["full_order"] == 25 and target_B == pattern["B"]
    assert len(mapping["centers"]) == pattern["centers"]
    assert target_faces == sorted(set(target_faces)) and len(target_faces) == len(pattern["faces"])
    assert all(0 < face < 1 << target_n and face.bit_count() == 3
               and face & ((1 << target_B)-1) for face in target_faces)
    validate(target_n, target_B, pattern["faces"], mapping, target_faces)
    images = {sum(1 << mapping["centers"][v] for v in range(pattern["centers"]) if face >> v & 1)
              for face in pattern["faces"]}
    assert images == set(target_faces)
    assert simple_holes(pattern["centers"], target_B, pattern["faces"]) == pattern["holes"]
    return {
        "verified": True, "pattern": pattern["id"], "full_order": 25, "B": target_B,
        "all_centers_and_anchor_rods_checked": True, "complete_outer_face_image_equal": True,
        "payment_requires_full_simple_disk_completion": True,
        "lower_mode": pattern["lower_mode"],
        "not_a_standalone_geometric_weak_graph_exclusion": True,
    }
