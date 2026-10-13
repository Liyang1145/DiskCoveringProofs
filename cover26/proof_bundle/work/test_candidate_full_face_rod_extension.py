"""Independent full native134rod bijection and existing angular-domain control.

No NEW inverse, energy bound, geometry interface or payment is accepted here.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import diagnose_candidate_full_face_rod_extension as producer
import n26_partial_prefix_quadratic_kernel as partial
import n26_sharp_partial_domains as independent
import n26_sharp_radius_constraints as constraints
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-candidate-full134rod-native-bijection-controls-v1"


def graph_gate(original, result):
    if (result["potential_NEW_vertices"] != 76 or result["potential_NEW_anchors"] != 16
            or result["potential_NEW_unrestricted_disk_centers"] != 26
            or result["potential_NEW_face_witnesses"] != 34
            or result["potential_NEW_free_vertices"] != 60
            or result["potential_NEW_positive_grounded_rod_count"] != 134
            or result["all_original92rods_retained_as_identical_prefix"] is not True
            or result["old_92rod_62vertex_46free_kernel_NOT_relabelled_or_replaced"] is not True
            or result["NEW_exact60by60inverse_harmonic_Schur_and_strict_bounds_NOT_computed"] is not True):
        raise ValueError("all-face structural control changed explicit new dimensions or old model scope")
    path = original["data"][3]
    full = path["states"][-1]
    spec = {"N": 26, "B": 16, "next": 26, "faces": full["faces"]}
    vertices, native_edges = partial.graph(spec)
    if vertices != 76 or len(native_edges) != 134:
        raise ValueError("independent actual full native graph changed its34face necessary rods")
    witness_by_face = {}
    for item in [*result["old_positive_support_face_witnesses"], *result["additional_face_witnesses"]]:
        face = tuple(item["actual_complete_face"])
        vertex = item.get("old_witness_vertex", item.get("new_witness_vertex"))
        if face in witness_by_face or type(vertex) is not int:
            raise ValueError("all-face structural control duplicated a face witness owner")
        witness_by_face[face] = vertex
    labels = {int(k): v for k, v in path["native_to_exact_candidate_labels"].items()}
    permutation = {anchor: anchor for anchor in range(16)}
    permutation.update({16+native: 16+physical for native, physical in labels.items()})
    for index, mask in enumerate(full["faces"], 42):
        face = tuple(sorted(labels[center] for center in range(26) if mask >> center & 1))
        if face not in witness_by_face:
            raise ValueError("all-face structural control omitted an actual complete native face")
        permutation[index] = witness_by_face[face]
    if (sorted(permutation) != list(range(76)) or sorted(permutation.values()) != list(range(76))
            or set(witness_by_face) != set(map(tuple, original["data"][0]["all_faces"]))):
        raise ValueError("all-face native76vertex relabel is not a full original-face bijection")
    mapped = {tuple(sorted((permutation[u], permutation[v]))) for u, v in native_edges}
    edges = result["potential_NEW_allface_rod_edges_DATA"]
    if (len(edges) != 134 or edges[:92] != original["reference"]["edges"]
            or len({tuple(sorted(edge)) for edge in edges}) != 134
            or {tuple(sorted(edge)) for edge in edges} != mapped):
        raise ValueError("all-face new edges disagree with the independent complete native necessary graph")
    return spec, permutation


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "caps", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("independent full-face graph controls changed fixed arithmetic DATA identity")
    original = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])["original"]
    diagnosis = binding.read(args.diagnosis)
    digest = binding.sha(args.diagnosis)
    if (diagnosis["schema"] != producer.SCHEMA
            or diagnosis["executed_diagnostic_sha256"] != binding.sha(producer.__file__)
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0
            or diagnosis["actual_old_forest_nodes_supports_and_paid_leaves_NOT_modified"] is not True):
        raise ValueError("independent full-face controls changed actual structural DATA producer or scope")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, expected in diagnosis["source_file_sha256"].items():
        if binding.sha(args.source / name) != expected or accepted["files"][name] != expected:
            raise ValueError("independent full-face controls changed actual latest source/history DATA")
    result = diagnosis["actual_structural_result"]
    spec, permutation = graph_gate(original, result)
    arcs = binding.force.load_trig(args.resource)[0]
    cap = binding.read(args.caps / "VERIFIED.json")
    cap_digest = binding.sha(args.caps / "VERIFIED.json")
    if (cap["verified"] is not True
            or cap["files"]["CERTIFICATE.json"] != binding.sha(args.caps / "CERTIFICATE.json")):
        raise ValueError("full-face angular control changed accepted same-root chord-cap DATA")
    caps, _ = constraints.cap_gate(original["radius"], binding.read(args.caps / "CERTIFICATE.json"), arcs)
    matrix, _ = constraints.constraint_matrix(spec, caps)
    other, _ = independent.matrix(spec, caps)
    if matrix is None or matrix != other:
        raise ValueError("full native34face graph angular matrices failed independent path reconstruction")
    rows = binding.read(args.source / "PENDING-ANGLES.json")
    states = [{"source_OPEN_index": row["index"],
               "additional_fullface_domain_empty": constraints.tighten(
                   matrix, row["sharp_lower"], row["sharp_upper"]) is None}
              for row in rows]
    negatives = []

    def reject(label, mutation):
        bad = deepcopy(result)
        mutation(bad)
        try:
            graph_gate(original, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid independent all-face rod graph accepted: "+label)

    for label, mutation in (
        ("fullface-extra-rod-omitted", lambda bad: bad["potential_NEW_allface_rod_edges_DATA"].pop()),
        ("fullface-old-rod-prefix-discarded", lambda bad: bad["potential_NEW_allface_rod_edges_DATA"].__setitem__(0, [62, 16])),
        ("fullface-new-rod-duplicated", lambda bad: bad["potential_NEW_allface_rod_edges_DATA"].__setitem__(-1, bad["potential_NEW_allface_rod_edges_DATA"][-2])),
        ("fullface-witness-owner-repeated", lambda bad: bad["additional_face_witnesses"][1].update(
            new_witness_vertex=bad["additional_face_witnesses"][0]["new_witness_vertex"])),
        ("fullface-actual-native-face-omitted", lambda bad: bad["additional_face_witnesses"].pop()),
        ("fullface-original46free-dimension-laundered", lambda bad: bad.update(potential_NEW_free_vertices=46)),
        ("fullface-new-inverse-falsely-claimed", lambda bad: bad.update(NEW_exact60by60inverse_harmonic_Schur_and_strict_bounds_NOT_computed=False)),
        ("fullface-original92rod-model-falsely-replaced", lambda bad: bad.update(old_92rod_62vertex_46free_kernel_NOT_relabelled_or_replaced=False)),
    ):
        reject(label, mutation)
    for name, expected in diagnosis["source_file_sha256"].items():
        if binding.sha(args.source / name) != expected:
            raise ValueError("actual source/history DATA changed during full-face graph controls")
    if binding.sha(args.diagnosis) != digest or binding.sha(args.caps / "VERIFIED.json") != cap_digest:
        raise ValueError("all-face structural or cap DATA changed during independent testing")
    report = {
        "schema": SCHEMA, "verified": False, "diagnosis_sha256": digest,
        "independent_complete_native134rod_and_exact76vertex_bijection_checked": True,
        "actual_native_to_extended_vertex_bijection_DATA": {str(k): v for k, v in permutation.items()},
        "original92rod_prefix_identical_and_all14new_faces_already_present": True,
        "full34face_angular_matrix_independently_reconstructed": True,
        "full34face_angular_matrix_already_identical_to_existing_necessary_matrix": matrix == original["matrix"],
        "actual_latest_source_root_DATA_count": len(rows),
        "actual_fullface_angular_root_DATA_states": states,
        "new_whole_roots_excluded_by_angular_tightening": sum(
            item["additional_fullface_domain_empty"] for item in states),
        "actual_independent_graph_scope_rejection_controls_passed": negatives,
        "NEW60by60inverse_NEW_weights_and_energy_bounds_NOT_computed_or_admitted": True,
        "old_source_forests_proofs_and_original92rod_kernel_UNMODIFIED": True,
        "complete_latest_model_source_history_geometry_acceptance_NOT_performed": True,
        "source_file_sha256": diagnosis["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"full134rod_independent_native_graph_controls_completed": True,
                      "actual_new_face_constraints": 14, "actual_rejections": len(negatives),
                      "full_angular_matrix_already_equal": matrix == original["matrix"],
                      "new_angular_exclusions": report["new_whole_roots_excluded_by_angular_tightening"],
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
