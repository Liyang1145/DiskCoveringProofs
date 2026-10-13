"""Independent full-replay acceptance of a fixed original arithmetic resource.

This is not a current candidate source. No root, leaf, transport subtree or
geometric lower-bound payment is discharged by this resource acceptance.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_owned_candidate_source as legacy
import n26_typed_arithmetic_context as codec
import verify_candidate_curvature_overlay as original
import verify_conditional_force_stage as binding


SCHEMA = "N26-original-candidate-arithmetic-resource-input-bindings-v1"
ACCEPTED = "N26-accepted-original-candidate-arithmetic-resource-v1"
EXPORT = "N26-unaccepted-original-candidate-arithmetic-context-export-v1"
SCOPE = "original-candidate-92-rods-same-root-Rstar"
read, sha, local_path = binding.read, binding.sha, binding.local_path


def projection(values):
    """Independently select exactly the fixed fields used by ENERGY/LOCAL."""
    frame, kernel = values[3], values[5]
    data = frame["data"]
    if (
        len(data) < 5
        or F(data[4]["unrestricted_center_neighbourhood_halfwidth_before_rotation"]) != F(7, 800000)
        or len(frame["matrix"]) != 16
        or len(frame["reference"]["edges"]) != 92
        or type(kernel["B"]) is not int or kernel["B"] != 16
        or type(kernel["vertices"]) is not int or kernel["vertices"] != 62
        or kernel["original_candidate_92_rod_46_free_vertex_kernel"] is not True
    ):
        raise ValueError("resource does not reconstruct the original frame and LOCAL allowance")
    return {
        "original": {
            "cap": frame["cap"], "reference": frame["reference"],
            "matrix": frame["matrix"], "radius": frame["radius"],
            "data": tuple(data[k] for k in range(5)),
        },
        "original_curvature_source_acceptance": values[2],
        "original_kernel": kernel,
    }


def payload_gate(payload, expected):
    result = codec.gate(payload)
    if payload != expected:
        raise ValueError("resource changes an independently reconstructed exact typed field")
    return result


def positive_gate(supplied, expected):
    if codec.pack(supplied) != codec.pack(expected):
        raise ValueError("resource changes the independently replayed original tiny-box control")


def node_at(payload, path):
    node = payload
    for key in path:
        if node[0] == "dict":
            node = next(value for name, value in node[1] if name == key)
        elif node[0] in ("list", "tuple") and type(key) is int:
            node = node[1][key]
        else:
            raise ValueError("control path is not a typed dictionary/container")
    return node


def replaced(payload, path, replacement):
    """Copy only the modified spine; never alter the accepted control payload."""
    if not path:
        return replacement
    key, rest = path[0], path[1:]
    if payload[0] == "dict":
        if sum(name == key for name, _ in payload[1]) != 1:
            raise ValueError("replacement control has no distinct dictionary key")
        return ["dict", [[name, replaced(value, rest, replacement) if name == key else value]
                         for name, value in payload[1]]]
    if payload[0] in ("list", "tuple") and type(key) is int:
        items = list(payload[1])
        items[key] = replaced(items[key], rest, replacement)
        return [payload[0], items]
    raise ValueError("replacement control has an invalid typed path")


def rejection_controls(expected, positive):
    rejected = []

    def reject(label, payload=None, changed_positive=None):
        try:
            if payload is not None:
                payload_gate(payload, expected)
            else:
                positive_gate(changed_positive, positive)
        except (ValueError, TypeError, KeyError, IndexError, OverflowError):
            rejected.append(label)
        else:
            raise AssertionError("invalid arithmetic resource accepted: " + label)

    reject("unknown-executable-context-tag", ["python", "never execute"])
    reject("duplicate-resource-dictionary-key",
           ["dict", [*expected[1], expected[1][0]]])
    reject("hidden-extra-resource-field",
           ["dict", [*expected[1], ["unproved", ["bool", True]]]])
    for label, path, value in (
        ("different-boundary-anchor-family", ("original_kernel", "B"), ["int", "15"]),
        ("different-original-vertex-frame", ("original_kernel", "vertices"), ["int", "63"]),
        ("kernel-boolean-promoted-to-integer",
         ("original_kernel", "original_candidate_92_rod_46_free_vertex_kernel"), ["int", "1"]),
        ("original-kernel-identity-flag-removed",
         ("original_kernel", "original_candidate_92_rod_46_free_vertex_kernel"), ["bool", False]),
        ("different-exact-radius", ("original", "radius"), ["fraction", "1", "4"]),
        ("original-LOCAL-allowance-enlarged",
         ("original", "data", 4, "unrestricted_center_neighbourhood_halfwidth_before_rotation"),
         ["str", "1/1000"]),
    ):
        reject(label, replaced(expected, path, value))
    edges = node_at(expected, ("original", "reference", "edges"))
    reject("one-original-rod-omitted", replaced(
        expected, ("original", "reference", "edges"), [edges[0], edges[1][:-1]]))
    data = node_at(expected, ("original", "data"))
    reject("original-data-tuple-relabelled-as-list",
           replaced(expected, ("original", "data"), ["list", data[1]]))
    reject("resource-dictionary-order-changed", ["dict", list(reversed(expected[1]))])
    reduced_positive = dict(positive)
    reduced_positive.pop(next(iter(reduced_positive)))
    reject("original-tiny-positive-control-field-omitted", changed_positive=reduced_positive)
    return rejected


def header_gate(export, manifest):
    if (
        export["schema"] != EXPORT or export["verified"] is not False
        or export["resource_scope"] != SCOPE
        or export["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
        or export["independent_resource_acceptance_and_actual_replay_still_required"] is not True
        or type(export["new_geometric_candidate_payments"]) is not int
        or export["new_geometric_candidate_payments"] != 0
        or type(export["current_candidate_roots_removed"]) is not int
        or export["current_candidate_roots_removed"] != 0
        or export["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or export["global_lower_bound_proved"] is not False
        or export["global_optimality_proved"] is not False
        or export["executed_producer_sha256"] != manifest["copied_files"][
            "propose_original_candidate_arithmetic_context.py"]
    ):
        raise ValueError("resource export was promoted to geometry or current-root ownership")
    for name in (
        "source", "source_replay", "source_acceptance_sha256", "source_current_audit",
        "source_current_audit_sha256", "source_final_digest_recheck",
        "source_final_digest_recheck_sha256",
    ):
        if export[name] != manifest[name]:
            raise ValueError("resource changed its immutable proof-time source identity: " + name)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    export = read(args.export)
    folder = local_path(export["source"])
    accepted, _ = binding.bound(folder)
    if (
        read(local_path(export["source_replay"])) != accepted
        or sha(folder / "VERIFIED.json") != export["source_acceptance_sha256"]
        or sha(local_path(export["source_current_audit"])) != export["source_current_audit_sha256"]
        or sha(local_path(export["source_final_digest_recheck"])) != export[
            "source_final_digest_recheck_sha256"]
    ):
        raise ValueError("resource builder changed its actual proof-time source or published replay")
    copies = {}

    def include(path, name):
        if name in copies and sha(copies[name]) != sha(path):
            raise ValueError("resource builder has conflicting sealed module bytes: " + name)
        copies[name] = path

    for name in accepted["files"]:
        if name.endswith(".py"):
            include(folder / name, name)
    for name in (
        "verify_original_candidate_arithmetic_context.py", "n26_current_owned_candidate_source.py",
        "n26_typed_arithmetic_context.py", "test_typed_arithmetic_context.py",
        "test_original_arithmetic_resource.py", "propose_original_candidate_arithmetic_context.py",
    ):
        include(Path(__file__).with_name(name), name)
    include(args.export, "EXPORT.json")
    include(args.codec_regression, "CODEC-REGRESSION.json")
    include(args.resource_regression, "RESOURCE-REGRESSION.json")
    include(Path(__file__).with_name("n26-original-arithmetic-resource-proof.md"), "PROOF.md")
    args.output.mkdir(parents=True)
    for name, path in copies.items():
        (args.output / name).write_bytes(path.read_bytes())
    manifest = {
        "schema": SCHEMA, "resource_scope": SCOPE, "export_original_path": linux(args.export),
        "export_sha256": sha(args.export),
        **{name: export[name] for name in (
            "source", "source_replay", "source_acceptance_sha256", "source_current_audit",
            "source_current_audit_sha256", "source_final_digest_recheck",
            "source_final_digest_recheck_sha256")},
        "copied_files": {name: sha(args.output / name) for name in copies},
    }
    header_gate(export, manifest)
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False,
                      "independent_full_legacy_replay_and_exact_typed_comparison_pending": True,
                      "new_geometric_candidate_payments": 0}), flush=True)


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != SCHEMA or manifest["resource_scope"] != SCOPE:
        raise ValueError("resource changed its fixed model scope")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("resource sealed input changed: " + name)
    for module in (legacy, codec, original, binding):
        if sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("resource executed different sealed legacy arithmetic")
    export = read(folder / "EXPORT.json")
    header_gate(export, manifest)
    initial = sha(local_path(manifest["source_current_audit"]))
    if (
        sha(folder / "EXPORT.json") != manifest["export_sha256"]
        or sha(local_path(manifest["export_original_path"])) != manifest["export_sha256"]
        or initial != manifest["source_current_audit_sha256"]
    ):
        raise ValueError("resource original export or proof-time checkpoint changed")
    print("Replaying the unchanged complete legacy source; resource earns zero geometry.", flush=True)
    accepted, values, pending, paths, _ = legacy.gate(
        local_path(manifest["source"]), local_path(manifest["source_replay"]),
        local_path(manifest["source_current_audit"]),
        local_path(manifest["source_final_digest_recheck"]),
    )
    expected = codec.pack(projection(values))
    model = payload_gate(export["typed_context"], expected)
    positive = original.tiny_control(values)
    positive_gate(export["original_tiny_box_positive_control"], positive)
    current = read(local_path(manifest["source_current_audit"]))
    if (
        type(export["source_checkpoint_remaining_whole_roots"]) is not int
        or export["source_checkpoint_remaining_whole_roots"] != len(pending)
        or export["source_checkpoint_pending_rows_sha256"] != sha(
            local_path(manifest["source"]) / "PENDING-ANGLES.json")
        or F(model["original"]["radius"]) != F(current["r_strict_interval"][1])
        or sha(local_path(manifest["source"]) / "VERIFIED.json") != manifest[
            "source_acceptance_sha256"]
    ):
        raise ValueError("resource changed its proof-time model or misidentified old root rows")
    codec_test = read(folder / "CODEC-REGRESSION.json")
    resource_test = read(folder / "RESOURCE-REGRESSION.json")
    if (
        codec_test["tested_codec_sha256"] != sha(codec.__file__)
        or codec_test["executed_test_sha256"] != manifest["copied_files"]["test_typed_arithmetic_context.py"]
        or len(codec_test["invalid_typed_context_controls_rejected"]) != 10
        or codec_test["new_geometric_candidate_payments"] != 0
        or resource_test["tested_resource_verifier_sha256"] != sha(__file__)
        or resource_test["executed_test_sha256"] != manifest["copied_files"][
            "test_original_arithmetic_resource.py"]
        or len(resource_test["invalid_resource_model_controls_rejected"]) != 13
        or resource_test["synthetic_only_not_an_actual_legacy_geometry_replay"] is not True
        or resource_test["new_geometric_candidate_payments"] != 0
    ):
        raise ValueError("resource codec/projection controls changed or were promoted to geometry")
    negatives = rejection_controls(expected, positive)
    semantic = {
        "schema": "N26-fixed-original-candidate-typed-arithmetic-model-v1",
        "resource_scope": SCOPE, "typed_context": expected,
        "original_tiny_box_positive_control": positive,
        "context_is_not_a_current_candidate_source_or_a_seed_history_substitute": True,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "new_geometric_candidate_payments": 0, "current_candidate_roots_removed": 0,
    }
    target = folder / "CONTEXT.json"
    if target.exists():
        if codec.pack(read(target)) != codec.pack(semantic):
            raise ValueError("resource actual publication semantic output changed")
    else:
        target.write_text(json.dumps(semantic, separators=(",", ":")) + "\n", encoding="utf-8")
    paths.extend(local_path(text) for text in export["files"])
    paths.extend(folder / name for name in manifest["copied_files"])
    paths.extend((folder / "MANIFEST.json", target, local_path(manifest["export_original_path"]),
                  local_path(manifest["source_replay"]),
                  local_path(manifest["source_current_audit"]),
                  local_path(manifest["source_final_digest_recheck"]), Path(__file__)))
    # Only duplicate file reads are factored. Every legacy semantic gate above
    # ran unchanged; none is replaced with a cache or a prior status marker.
    raw_paths = {str(path): path for path in paths}
    unique = {linux(path): path for path in raw_paths.values()}
    print("Binding the final distinct original and sealed resource dependencies.", flush=True)
    inventory = {text: sha(path) for text, path in unique.items()}
    if any(inventory.get(text) != digest for text, digest in export["files"].items()):
        raise ValueError("resource original producer inventory changed during independent replay")
    for text, digest in inventory.items():
        if sha(text) != digest:
            raise ValueError("resource dependency changed during final binding: " + text)
    if sha(local_path(manifest["source_current_audit"])) != initial:
        raise ValueError("resource proof-time checkpoint changed during full semantic replay")
    report = {
        "schema": ACCEPTED, "verified": True, "resource_scope": SCOPE,
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_current_audit_sha256": initial,
        "source_final_digest_recheck_sha256": manifest["source_final_digest_recheck_sha256"],
        "all_legacy_source_geometry_and_prior_payments_independently_replayed": True,
        "entire_exact_typed_original_model_and_kernel_reconstructed_identically": True,
        "original_tiny_box_positive_control_reconstructed_identically": True,
        "source_checkpoint_remaining_whole_roots": len(pending),
        "source_checkpoint_root_count_not_a_current_candidate_count": True,
        "context_is_not_a_current_candidate_source_or_a_seed_history_substitute": True,
        "resource_acceptance_is_not_a_faster_current_source_interface": True,
        "radius_upper": str(model["original"]["radius"]),
        "r_strict_interval": current["r_strict_interval"],
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "negative_controls_rejected": negatives,
        "new_geometric_candidate_payments": 0, "current_candidate_roots_removed": 0,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: sha(folder / name) for name in (
            "MANIFEST.json", *manifest["copied_files"], "CONTEXT.json")},
        "source_files": inventory, "executed_checker_sha256": sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"][Path(__file__).name]:
        raise ValueError("resource did not execute its own frozen checker")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files")}, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("export", "codec-regression", "resource-regression", "output"):
        builder.add_argument("--" + name, type=Path, required=True)
    verifier = commands.add_parser("verify")
    verifier.add_argument("--input", type=Path, required=True)
    verifier.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "build":
        build(args)
    else:
        verify(args.input, args.report)


if __name__ == "__main__":
    main()
