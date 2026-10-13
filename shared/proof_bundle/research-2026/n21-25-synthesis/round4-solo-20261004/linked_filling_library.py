"""Stdlib exact acceptance/lookup for complete linked filling family theorems."""
from pathlib import Path
from fractions import Fraction as F
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical, validate
from linked_general_collar_kernel import replay, start_states
from n25_outer_search import read, bind, unchanged

assert __debug__


def validate_exact_outer_map(pattern, target_order, target_B, target_label_bound, target_faces, mapping):
    assert target_order == pattern["full_order"] == 25
    assert target_B == pattern["B"] and target_B <= target_label_bound <= target_order
    assert target_faces == sorted(set(target_faces)) and target_faces
    assert len(mapping["centers"]) == pattern["centers"] and len(mapping["anchors"]) == target_B
    assert all(type(mask) is int and 0 < mask < 1 << target_label_bound and mask.bit_count() == 3
               and mask & ((1 << target_B)-1) for mask in target_faces)
    used = 0
    for mask in target_faces:
        used |= mask
    assert used.bit_count() == pattern["centers"]
    assert used & ((1 << target_B)-1) == (1 << target_B)-1
    validate(target_label_bound, target_B, pattern["faces"], mapping, target_faces)
    images = sorted(sum(1 << mapping["centers"][v]
                        for v in range(pattern["centers"]) if mask >> v & 1)
                    for mask in pattern["faces"])
    assert images == target_faces
    remaining = sorted(set(range(target_B, 25))-set(mapping["centers"][target_B:]))
    extended = mapping["centers"]+remaining
    assert len(extended) == 25 and sorted(extended) == list(range(25))
    return {
        "verified": True, "pattern": pattern["id"], "N": 25, "B": target_B,
        "all_outer_center_anchor_and_face_maps_checked": True,
        "exact_complete_outer_face_image_equal": True,
        "center_map_extended_bijectively_to_all25_labels": extended,
        "requires_complete_same_order_simple_disk_completion": True,
        "lower_mode": pattern["lower_mode"],
        "not_a_standalone_geometric_weak_graph_exclusion": True,
    }


def make_index(library):
    index = {}
    for pattern in library["patterns"]:
        key = (pattern["B"], pattern["centers"], tuple(pattern["faces"]))
        assert key not in index
        index[key] = pattern
    assert len(index) == library["pattern_count"]
    return index


def lookup_exact_outer(index, target_order, target_B, target_label_bound, target_faces):
    assert target_order == 25 and target_B in (14, 15, 16, 17)
    assert target_B <= target_label_bound <= 25
    assert target_faces and target_faces == sorted(set(target_faces))
    assert all(type(mask) is int and 0 < mask < 1 << target_label_bound and mask.bit_count() == 3
               and mask & ((1 << target_B)-1) for mask in target_faces)
    code, mapping = canonical(target_label_bound, target_B, target_faces, 1)
    pattern = index.get((target_B, len(mapping["centers"]), code))
    if pattern is None:
        return None
    checked = validate_exact_outer_map(pattern, target_order, target_B, target_label_bound, target_faces, mapping)
    return pattern, mapping, checked


def library_gate(path):
    path = path.resolve()
    assert path.is_relative_to(ROOT)
    library = read(path)
    assert library["verified"] and library["schema"] == "strict-linked-completion-exact-collar-library-v1"
    assert library["source_sha256"] == sha(ROOT / "export_linked_filling_library.py")
    assert library["full_order"] == 25 and library["exact_N_B_and_outer_image_required"]
    assert library["all_patterns_pay_complete_linked_filling_families"]
    assert library["not_a_complete_competitor_family_or_union"]
    assert library["pattern_count"] == len(library["patterns"]) > 0
    assert library["transport_source_sha256"] == sha(ROOT / "LINKED-FILLING-EXACT-COLLAR-TRANSPORT.md")
    files = dict(library["files_relative_to_workspace"])
    unchanged(files)
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 25
    assert F(constants["radius_upper"]) == F(library["radius_upper_threshold"]) == F(239146311738101, 10**15)
    seen = set()
    for pattern in library["patterns"]:
        assert pattern["id"] == len(seen) and pattern["full_order"] == 25
        B, centers, faces = pattern["B"], pattern["centers"], pattern["faces"]
        assert B in (14, 15, 16, 17) and B <= centers <= 25
        assert pattern["lower_mode"] == "no_full_same_order_simple_disk_with_all_rods_at_most_U25"
        assert pattern["not_a_standalone_geometric_weak_graph_exclusion"]
        key = (B, centers, tuple(faces))
        assert key not in seen
        seen.add(key)
        code, mapping = canonical(centers, B, faces, 1)
        assert tuple(faces) == code and len(mapping["centers"]) == centers
        validate(centers, B, faces, mapping, faces)
        start_states(25, B, centers, faces)
        proof_path = ROOT.parents[2] / pattern["proof_file_relative_to_workspace"]
        assert sha(proof_path) == pattern["proof_sha256"]
        payload = read(proof_path)
        assert payload["constants_sha256"] == sha(constants_path)
        assert payload["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
        assert (payload["N"], payload["B"], payload["collar_centers"], payload["collar_faces"]) == (
            25, B, centers, faces)
        result = replay(proof_path, constants)
        assert result == pattern["fresh_exact_branch_replay"]
        assert result["all_full_simple_disk_completions_strictly_paid"]
        assert result["pending_complete_leaves"] == result["unsearched_frontier_nodes"] == 0
    make_index(library)
    for item in (path, Path(__file__), constants_path, ROOT / "LINKED-FILLING-EXACT-COLLAR-TRANSPORT.md"):
        bind(files, item)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    return library, files
