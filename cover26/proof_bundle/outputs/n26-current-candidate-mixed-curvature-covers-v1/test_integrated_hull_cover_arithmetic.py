"""Independent arithmetic-only reconstruction and invalid integrated covers."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_integrated_hull_curvature as integrated
import n26_signed_hull_local_cover as partition
import n26_typed_arithmetic_context as codec
import probe_candidate_integrated_hull_local_cover as probe
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def replay(original, kernel, arcs, actual_row, item):
    if (item["source_OPEN_index"] != actual_row["index"]
            or item["actual_source_closed_box"] != actual_row):
        raise ValueError("integrated arithmetic cover changed actual whole-root ownership/domain")
    root_box = partition.tighten(
        original["matrix"], actual_row["sharp_lower"], actual_row["sharp_upper"])
    reference = list(map(F, item["reference_turns"]))
    raw = item["uniform_integral_root_curvature_certificate"]
    eta = list(map(F, raw["signed_eta"]))
    fresh = integrated.gate(
        kernel, original["matrix"], reference, *root_box, eta, arcs, raw["parts"])
    if fresh != raw:
        raise ValueError("integrated Taylor weights, strips or rounding certificate changed")
    parts, central = partition.partition(
        original["matrix"], actual_row, item, partition.tighten)
    other_parts, other_central = partition.partition(
        original["matrix"], actual_row, item, partition.independently_contract)
    if parts != other_parts or central != other_central:
        raise ValueError("integrated independent exact closed partitions disagree")
    margins, count = [], 0
    for slab, box in zip(item["sequential_closed_slabs"], parts):
        if box is None:
            if slab["kind"] != "EMPTY":
                raise ValueError("integrated empty slab labelled as nonempty energy")
            continue
        if (slab["kind"] != "INTEGRATED-HULL-ENERGY"
                or slab["sharp_lower"] != list(map(str, box[0]))
                or slab["sharp_upper"] != list(map(str, box[1]))):
            raise ValueError("integrated slab clipped its full closed domain")
        result = probe.slab_bound(
            kernel, original["matrix"], reference, root_box, box, eta,
            original["radius"], arcs)
        if (result != slab["arithmetic_result"]
                or not result["arithmetic_strict_slab_test_passed"]
                or F(result["strict_energy_margin"]) <= 0
                or F(result["strict_radius_margin"]) <= 0):
            raise ValueError("integrated full slab lacks fresh strict exact energy/radius margins")
        margins.append(F(result["strict_radius_margin"]))
        count += 1
    local = partition.forest.local_proof(original, *central)
    if local != item["central_closed_box"]["original_LOCAL_result"]:
        raise ValueError("integrated central original LOCAL certificate changed")
    return {
        "source_OPEN_index": actual_row["index"],
        "strict_integrated_slabs_checked": count,
        "minimum_strict_radius_margin": str(min(margins)),
        "original_LOCAL_entry_margin": local["strict_original_LOCAL_entry_margin"],
        "two_exact_closed_partitions_and_uniform_integral_root_gate_checked": True,
    }


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
        raise ValueError("integrated test changed fixed resource/model identity or zero-source scope")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    digest = binding.sha(args.current_audit)
    layer = identity.gate(binding.read(args.current_audit), digest, args.source)
    pending = {row["index"]: row for row in binding.read(args.source / "PENDING-ANGLES.json")}
    diagnosis = binding.read(args.diagnosis)
    if (diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["actual_current_audit_sha256"] != digest
            or diagnosis["executed_probe_sha256"] != binding.sha(probe.__file__)
            or diagnosis["modules"][linux(Path(integrated.__file__))]
            != binding.sha(integrated.__file__)):
        raise ValueError("integrated test changed its actual diagnostic/module identity")
    arcs = binding.force.load_trig(args.resource)[0]
    results = [replay(original, kernel, arcs, pending[item["source_OPEN_index"]], item)
               for item in diagnosis["roots"]]
    first = diagnosis["roots"][0]
    row = pending[first["source_OPEN_index"]]
    rejected = []

    def reject(name, mutation):
        bad = deepcopy(first)
        mutation(bad)
        try:
            replay(original, kernel, arcs, row, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(name)
        else:
            raise AssertionError("invalid integrated cover accepted: " + name)

    reject("whole-root-ownership-changed",
           lambda bad: bad.update(source_OPEN_index=row["index"] + 1))
    reject("first-closed-slab-omitted",
           lambda bad: bad["sequential_closed_slabs"].pop(0))
    reject("shared-slab-boundary-lost",
           lambda bad: bad["sequential_closed_slabs"][0].update(
               both_closed_halves_include_shared_cut=False))
    reject("central-remainder-clipped",
           lambda bad: bad["central_closed_box"]["closed_lower"].__setitem__(0, "0"))
    reject("Taylor-strip-omitted",
           lambda bad: bad["uniform_integral_root_curvature_certificate"]["closed_Taylor_strips"].pop(0))
    reject("Taylor-weight-unjustifiably-increased",
           lambda bad: bad["uniform_integral_root_curvature_certificate"]["closed_Taylor_strips"][0].update(
               normalized_Taylor_weight="1"))
    reject("weighted-rounding-operator-error-omitted",
           lambda bad: bad["uniform_integral_root_curvature_certificate"].update(
               weighted_symmetric_rounding_operator_error_charged="0"))
    reject("nonpositive-Taylor-partition-count",
           lambda bad: bad["uniform_integral_root_curvature_certificate"].update(parts=0))
    free = next(axis for axis, value in enumerate(
        first["uniform_integral_root_curvature_certificate"]["signed_eta"]) if F(value) < 0)
    reject("unsupported-integrated-positive-curvature",
           lambda bad: bad["uniform_integral_root_curvature_certificate"]["signed_eta"].__setitem__(
               free, "-1000000"))
    reject("infeasible-reference-outside-necessary-polytope",
           lambda bad: bad["reference_turns"].__setitem__(0, "100"))
    reject("strict-energy-margin-fabricated",
           lambda bad: bad["sequential_closed_slabs"][0]["arithmetic_result"].update(
               strict_energy_margin="1"))
    reject("original-LOCAL-allowance-expanded",
           lambda bad: bad["central_closed_box"]["original_LOCAL_result"].update(
               original_52_coordinate_local_allowance="1"))
    if binding.sha(args.current_audit) != digest:
        raise ValueError("current snapshot changed during integrated arithmetic reconstruction")
    report = {
        "schema": "N26-independent-integrated-hull-LOCAL-arithmetic-controls-v1",
        "all_arithmetic_cover_reconstructions_passed": True, "results": results,
        "strict_integrated_slabs_checked": sum(
            result["strict_integrated_slabs_checked"] for result in results),
        "original_LOCAL_central_boxes_checked": len(results),
        "rejection_controls_passed": rejected,
        "actual_current_audit_sha256": digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "diagnosis_sha256": binding.sha(args.diagnosis),
        "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "arithmetic_only_NOT_geometry_or_complete_source_history_replay": True,
        "verified": False, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0, "global_optimality_proved": False,
        "existing_constant_hull_supplemental_verifier_does_NOT_accept_this_mode": True,
        "executed_test_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (integrated, integrated.hull, partition, codec, identity, probe)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("modules", "results")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
