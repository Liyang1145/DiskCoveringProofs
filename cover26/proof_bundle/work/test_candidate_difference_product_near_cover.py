"""Independent exact reconstruction of a proper near-root subbox, zero payments."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_difference_product_curvature as product
import n26_signed_hull_local_cover as partition
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_difference_product_curvature as producer
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def replay(original, kernel, arcs, actual_row, record):
    if (record["source_OPEN_index"] != actual_row["index"]
            or record["actual_source_closed_box"] != actual_row
            or record["outside_near_SUBBOX_whole_root_obligations_NOT_proved"] is not True
            or record["source_entire_whole_root_REMOVED"] is not False):
        raise ValueError("product near-cover changed owner or pretended whole-root completion")
    near = record["near_reference_SUBBOX_diagnosis"]
    whole = tighten(original["matrix"], actual_row["sharp_lower"], actual_row["sharp_upper"])
    box = tighten(original["matrix"], near["closed_lower"], near["closed_upper"])
    if (box is None or box == whole
            or near["proper_subbox_only_NOT_entire_actual_source_root"] is not True
            or any(a < wa or c > wc for a, c, wa, wc in zip(*box, *whole))):
        raise ValueError("product near-cover must be a properly contained source subbox")
    synthetic_row = {**actual_row, "sharp_lower": list(map(str, box[0])),
                     "sharp_upper": list(map(str, box[1]))}
    cover = {"source_OPEN_index": actual_row["index"],
             "actual_source_closed_box": synthetic_row,
             "sequential_closed_slabs": near["sequential_closed_slabs"],
             "central_closed_box": near["central_closed_box"]}
    parts, central = partition.partition(original["matrix"], synthetic_row, cover, tighten)
    others, other_central = partition.partition(
        original["matrix"], synthetic_row, cover, partition.independently_contract)
    if parts != others or central != other_central:
        raise ValueError("product near-cover independent closed partitions disagree")
    strict = 0
    for slab, slab_box in zip(near["sequential_closed_slabs"], parts):
        if slab_box is None:
            if slab["kind"] != "EMPTY":
                raise ValueError("empty near-slab has a nonempty geometry label")
            continue
        if (slab["kind"] != "DIFFERENCE-PRODUCT-ENERGY"
                or slab["sharp_lower"] != list(map(str, slab_box[0]))
                or slab["sharp_upper"] != list(map(str, slab_box[1]))):
            raise ValueError("product near-slab changed the whole closed leaf domain")
        result = product.bound(
            kernel, original["matrix"], *slab_box, slab["certificate"], original["radius"], arcs)
        if (result != slab["arithmetic_result"]
                or not result["arithmetic_strict_target_test_passed"]):
            raise ValueError("product near-slab strict arithmetic/result did not reconstruct")
        strict += 1
    local = partition.forest.local_proof(original, *central)
    if local != near["central_closed_box"]["original_LOCAL_result"]:
        raise ValueError("product near-cover original LOCAL result changed")
    return {
        "source_OPEN_index": actual_row["index"],
        "proper_near_SUBBOX_only_arithmetic_cover_reconstructed": True,
        "strict_product_energy_slabs_checked": strict,
        "original_LOCAL_central_box_checked": True,
        "outside_near_SUBBOX_whole_root_still_unproved": True,
        "original_LOCAL_entry_margin": local["strict_original_LOCAL_entry_margin"],
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "diagnosis", "report"):
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
        raise ValueError("near product test changed zero-source resource/model identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    accepted = binding.read(args.source / "VERIFIED.json")
    if binding.sha(args.source / "PENDING-ANGLES.json") != accepted["files"]["PENDING-ANGLES.json"]:
        raise ValueError("near product test changed actual remaining source row DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json") if row["index"] == 29)
    diagnosis = binding.read(args.diagnosis)
    if (diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__)):
        raise ValueError("near product test changed diagnostic scope/executor")
    record = next(item for item in diagnosis["results"] if item["source_OPEN_index"] == 29)
    arcs = binding.force.load_trig(args.resource)[0]
    result = replay(original, kernel, arcs, row, record)
    rejected = []

    def reject(name, mutation):
        bad = deepcopy(record)
        mutation(bad)
        try:
            replay(original, kernel, arcs, row, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(name)
        else:
            raise AssertionError("invalid near-subbox cover accepted: " + name)

    reject("proper-subbox-promoted-to-whole-root",
           lambda bad: bad.update(outside_near_SUBBOX_whole_root_obligations_NOT_proved=False))
    reject("source-root-falsely-removed",
           lambda bad: bad.update(source_entire_whole_root_REMOVED=True))
    reject("lost-closed-energy-slab",
           lambda bad: bad["near_reference_SUBBOX_diagnosis"]["sequential_closed_slabs"].pop(0))
    reject("lost-shared-cut-boundary",
           lambda bad: bad["near_reference_SUBBOX_diagnosis"]["sequential_closed_slabs"][0].update(
               both_closed_halves_include_shared_cut=False))
    reject("negative-product-multiplier",
           lambda bad: bad["near_reference_SUBBOX_diagnosis"]["sequential_closed_slabs"][0][
               "certificate"]["products"][0].update(multiplier="-1"))
    reject("nonzero-reference-product-charge-omitted",
           lambda bad: bad["near_reference_SUBBOX_diagnosis"]["sequential_closed_slabs"][0][
               "arithmetic_result"].update(reference_product_constant_charged="0"))
    reject("original-LOCAL-allowance-expanded",
           lambda bad: bad["near_reference_SUBBOX_diagnosis"]["central_closed_box"][
               "original_LOCAL_result"].update(original_52_coordinate_local_allowance="1"))
    reject("proper-subbox-clipped-outside-actual-source",
           lambda bad: bad["near_reference_SUBBOX_diagnosis"]["closed_lower"].__setitem__(0, "-1"))
    report = {
        "schema": "N26-independent-proper-near-subbox-product-LOCAL-arithmetic-controls-v1",
        **result, "invalid_subbox_controls_rejected": rejected,
        "diagnosis_sha256": binding.sha(args.diagnosis),
        "complete_latest_model_source_history_replay_NOT_performed": True,
        "running_mixed_acceptance_does_NOT_admit_this_product_mode": True,
        "verified": False, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0, "global_optimality_proved": False,
        "tested_product_module_sha256": binding.sha(product.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
