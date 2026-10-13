"""Exact structural DATA for a distinct all34face necessary rod extension.

Preserve the accepted 92-rod model. This diagnostic does not replace it, add
an accepted kernel, mutate a forest or import stale ownership from the resource.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from n26_force import CAPS, D
import n26_current_candidate_layer_identity as identity
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-actual-candidate-all34face-rod-extension-structural-diagnosis-v1"


def reconstruct(system, reference, path):
    if (reference["N"] != 26 or reference["B"] != 16
            or len(reference["edges"]) != 92 or len(reference["weight_numerators"]) != 92):
        raise ValueError("all-face extension changed the original 92-rod source model")
    mapping = {int(k): v for k, v in path["native_to_exact_candidate_labels"].items()}
    if sorted(mapping) != list(range(26)) or sorted(mapping.values()) != list(range(26)):
        raise ValueError("all-face extension changed the actual source-to-exact center bijection")
    if any(mapping[index] != index for index in range(16)):
        raise ValueError("all-face extension changed the original boundary anchor/center order")
    final = path["states"][-1]
    if (final["prefix"] != path["prefix"] or final["terminal"] is not True
            or final["next"] != 26 or final["pending"] or len(final["faces"]) != 34):
        raise ValueError("all-face extension has no actual complete34face candidate terminal")
    native = OriginReference(26, 16, "dfs", caps=CAPS, scale=D)
    state = native.resolve(tuple(final["prefix"]))
    if native.entry(tuple(final["prefix"]), state, native.children(state)) != final:
        raise ValueError("all-face extension actual complete terminal failed independent recurrence")
    faces = [tuple(face) for face in system["all_faces"]]
    if (len(faces) != 34 or len(set(faces)) != 34
            or any(len(face) != 3 or list(face) != sorted(set(face))
                   or any(type(index) is not int or not 0 <= index < 26 for index in face) for face in faces)):
        raise ValueError("all-face extension has missing, repeated or malformed exact candidate faces")
    mapped = {
        tuple(sorted(mapping[index] for index in range(26) if mask >> index & 1))
        for mask in final["faces"]
    }
    if mapped != set(faces):
        raise ValueError("all34exact faces do not match the actual complete transport terminal bijection")
    slack_records = system["slack_faces"]
    if (not isinstance(slack_records, list)
            or any(not isinstance(item, dict)
                   or set(item) != {"face", "floating_squared_slack"}
                   or not isinstance(item["face"], list) for item in slack_records)):
        raise ValueError("all-face source slack classification has unknown structured DATA fields")
    active = set(map(tuple, system["active_faces"]))
    slack = {tuple(item["face"]) for item in slack_records}
    if active & slack or active | slack != set(faces):
        raise ValueError("all-face source active/slack classification lost an actual complete face")
    old_edges = reference["edges"]
    normalized = {tuple(sorted(edge)) for edge in old_edges}
    if len(normalized) != 92:
        raise ValueError("original accepted92rod source repeats an edge")
    witnesses = {}
    boundary = {index: set() for index in range(16)}
    for edge in old_edges:
        if (not isinstance(edge, list) or len(edge) != 2
                or any(type(index) is not int or not 0 <= index < 62 for index in edge)):
            raise ValueError("all-face extension changed an original actual rod endpoint")
        u, v = edge
        if 42 <= u < 62 and 16 <= v < 42:
            witnesses.setdefault(u, set()).add(v-16)
        elif 0 <= u < 16 and 16 <= v < 32:
            boundary[u].add(v-16)
        else:
            raise ValueError("original92rod source has an unknown anchor/center/face-witness edge")
    if (set(witnesses) != set(range(42, 62))
            or any(len(vertices) != 3 for vertices in witnesses.values())
            or any(boundary[index] != {index, (index+1) % 16} for index in range(16))):
        raise ValueError("original92rod face or boundary source cannot be reconstructed exactly")
    selected = [tuple(sorted(witnesses[index])) for index in range(42, 62)]
    if len(set(selected)) != 20 or not set(selected) <= set(faces):
        raise ValueError("original20positive-support faces are not a distinct actual all34face subset")
    missing = [face for face in faces if face not in set(selected)]
    if len(missing) != 14:
        raise ValueError("all-face extension changed the expected14missing witness constraints")
    extended = deepcopy(old_edges)
    new_witnesses = []
    for index, face in enumerate(missing, 62):
        extended.extend([[index, 16+center] for center in face])
        new_witnesses.append({"new_witness_vertex": index, "actual_complete_face": list(face)})
    adjacency = [set() for _ in range(76)]
    for u, v in extended:
        adjacency[u].add(v)
        adjacency[v].add(u)
    seen, queue = set(range(16)), list(range(16))
    for u in queue:
        for v in adjacency[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    if (len(extended) != 134 or len({tuple(sorted(edge)) for edge in extended}) != 134
            or len(seen) != 76 or extended[:92] != old_edges):
        raise ValueError("all-face extension omitted an old rod, lost grounding or repeated a new constraint")
    return {
        "actual_complete_source_face_count": 34,
        "source_active_face_count": len(active), "source_slack_face_count": len(slack),
        "source_floating_slack_values_are_DATA_NOT_geometric_inequality_proofs": True,
        "old_positive_support_face_count": 20,
        "old_positive_support_face_witnesses": [
            {"old_witness_vertex": vertex, "actual_complete_face": list(face)}
            for vertex, face in zip(range(42, 62), selected)],
        "additional_actual_complete_face_count": 14,
        "additional_face_witnesses": new_witnesses,
        "all_original92rods_retained_as_identical_prefix": True,
        "potential_NEW_allface_rod_edges_DATA": extended,
        "potential_NEW_vertices": 76, "potential_NEW_anchors": 16,
        "potential_NEW_unrestricted_disk_centers": 26,
        "potential_NEW_face_witnesses": 34, "potential_NEW_free_vertices": 60,
        "potential_NEW_positive_grounded_rod_count": 134,
        "every_NEW_face_is_already_present_in_the_actual_complete_terminal": True,
        "all_NEW_free_vertices_have_actual_paths_to_original_anchors": True,
        "actual_complete_native_to_exact_face_bijection_and_boundary_order_checked": True,
        "old_92rod_62vertex_46free_kernel_NOT_relabelled_or_replaced": True,
        "NEW_exact60by60inverse_harmonic_Schur_and_strict_bounds_NOT_computed": True,
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "report"):
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
        raise ValueError("all-face structural diagnosis changed fixed arithmetic model DATA identity")
    original = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])["original"]
    current, current_digest = binding.read(args.current_audit), binding.sha(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("all-face structural diagnosis changed actual same-root radius")
    accepted = binding.read(args.source / "VERIFIED.json")
    source_files = {name: binding.sha(args.source / name)
                    for name in ("PENDING-ANGLES.json", "PROPOSAL.json", "SOURCE-ROOT-HISTORY.json")}
    if any(accepted["files"][name] != digest for name, digest in source_files.items()):
        raise ValueError("all-face structural diagnosis changed actual newest source/history DATA")
    result = reconstruct(original["data"][0], original["reference"], original["data"][3])
    negative = []

    def reject(label, mutation):
        system, reference, path = deepcopy(original["data"][0]), deepcopy(original["reference"]), deepcopy(original["data"][3])
        mutation(system, reference, path)
        try:
            reconstruct(system, reference, path)
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual full-face source extension accepted: "+label)

    for label, mutation in (
        ("allface-one-complete-face-omitted", lambda s, r, p: s["all_faces"].pop()),
        ("allface-complete-face-duplicated", lambda s, r, p: s["all_faces"].__setitem__(0, s["all_faces"][1])),
        ("allface-original-positive-rod-omitted", lambda s, r, p: r["edges"].pop()),
        ("allface-native-center-bijection-broken", lambda s, r, p: p["native_to_exact_candidate_labels"].update({"16": 0})),
        ("allface-source-nonterminal-promoted-to-complete", lambda s, r, p: p["states"].__setitem__(-1, p["states"][-2])),
        ("allface-active-slack-classification-overlapped", lambda s, r, p: s["slack_faces"].append(
            {"face": s["active_faces"][0], "floating_squared_slack": 0.0})),
        ("allface-original-boundary-rod-relabelled", lambda s, r, p: r["edges"][-1].__setitem__(1, 16)),
    ):
        reject(label, mutation)
    for name, digest in source_files.items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("actual source/history DATA changed during all-face structural diagnosis")
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("actual completed current snapshot changed during all-face structural diagnosis")
    report = {
        "schema": SCHEMA, "verified": False,
        "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "source_file_sha256": source_files, "actual_structural_result": result,
        "actual_structural_rejection_controls_passed": negative,
        "fixed_resource_DATA_NOT_latest_source_ownership_cache": True,
        "actual_old_forest_nodes_supports_and_paid_leaves_NOT_modified": True,
        "new_kernel_weights_inverse_energy_certificates_and_geometry_interface_still_required": True,
        "global_necessity_transport_and_complete_latest_model_source_history_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_diagnostic_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_candidate_allface_structural_diagnosis_completed": True,
                      "old_positive_support_faces": 20, "additional_actual_complete_faces": 14,
                      "potential_NEW_vertices": 76, "potential_NEW_rods": 134,
                      "actual_rejections": len(negative), "verified": False, "new_geometric_payments": 0}),
          flush=True)


if __name__ == "__main__":
    main()
