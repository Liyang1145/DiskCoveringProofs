"""Preserve the adaptive diagnosis and try exact zero-dual alternatives.

Any solver-suggested dual can be inferior to zero. This fresh diagnostic does
not change old reports, source history, accepted forests or current counts.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_signed_hull_local_cover as cover
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "diagnosis", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
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
        raise ValueError("zero-dual diagnosis changed fixed resource/model bytes or scope")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    layer = identity.gate(binding.read(args.current_audit), current_digest, args.source)
    pending = {row["index"]: row for row in binding.read(args.source / "PENDING-ANGLES.json")}
    diagnosis = binding.read(args.diagnosis)
    if (diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["actual_current_audit_sha256"] != current_digest
            or diagnosis["modules"][linux(Path(cover.hull.__file__))] != binding.sha(cover.hull.__file__)
            or diagnosis["modules"][linux(Path(cover.__file__))] != binding.sha(cover.__file__)):
        raise ValueError("zero-dual diagnosis changed its unaccepted parent or exact lemmas")
    arcs = binding.force.load_trig(args.resource)[0]
    roots, repairs = deepcopy(diagnosis["roots"]), []
    for item in roots:
        root = item["source_OPEN_index"]
        if item["actual_source_closed_box"] != pending[root]:
            raise ValueError("zero-dual diagnosis changed an actual current whole-root row")
        for index, slab in enumerate(item["sequential_closed_slabs"]):
            if slab["arithmetic_obligation_passed"]:
                continue
            if slab["kind"] != "SIGNED-HULL-ENERGY":
                raise ValueError("zero-dual alternative requires a nonempty exact slab")
            cert = {**slab["certificate"], "difference_dual": {"q": 1, "terms": []}}
            result = cover.hull.bound(
                kernel, original["matrix"], slab["sharp_lower"], slab["sharp_upper"],
                cert, original["radius"], arcs)
            if result["arithmetic_strict_exclusion_test_passed"]:
                repairs.append({"source_OPEN_index": root, "slab_index": index,
                                "old_certificate": slab["certificate"],
                                "old_arithmetic_result": slab["arithmetic_result"]})
                slab.update(certificate=cert, arithmetic_result=result,
                            arithmetic_obligation_passed=True,
                            zero_dual_alternative_chosen=True)
        item["all_arithmetic_cover_obligations_passed"] = all(
            slab["arithmetic_obligation_passed"] for slab in item["sequential_closed_slabs"]
        ) and item["central_closed_box"]["original_LOCAL_arithmetic_check_passed"]
        if item["all_arithmetic_cover_obligations_passed"]:
            item["independent_arithmetic_cover_replay"] = cover.replay(
                original, kernel, arcs, pending[root], item)
        print(json.dumps({"root": root,
                          "all_cover_arithmetic_checks_passed":
                              item["all_arithmetic_cover_obligations_passed"],
                          "verified": False, "new_geometric_payments": 0}), flush=True)
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("current audit changed during zero-dual alternative diagnosis")
    report = {
        **diagnosis,
        "schema": "N26-unaccepted-adaptive-signed-hull-LOCAL-zero-dual-diagnosis-v1",
        "roots": roots, "exact_zero_dual_alternative_receipts": repairs,
        "parent_diagnosis_sha256": binding.sha(args.diagnosis),
        "all_arithmetic_cover_roots_passed": sum(
            item["all_arithmetic_cover_obligations_passed"] for item in roots),
        "actual_latest_candidate_layer_identity_only": layer,
        "verified": False, "new_geometric_payments": 0,
        "current_candidate_whole_roots_removed": 0,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (cover, cover.hull, cover.forest, codec, identity)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"diagnosis_completed": True,
                      "all_arithmetic_cover_roots_passed": report["all_arithmetic_cover_roots_passed"],
                      "slabs_improved_with_exact_zero_dual": len(repairs),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
