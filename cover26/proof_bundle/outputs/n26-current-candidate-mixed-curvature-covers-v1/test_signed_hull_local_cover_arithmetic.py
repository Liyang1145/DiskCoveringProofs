"""Independent arithmetic reconstruction of unaccepted hull/LOCAL diagnoses."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_signed_hull_local_cover as cover
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as curvature_probe
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
    if (binding.sha(args.resource / "VERIFIED.json") != curvature_probe.RESOURCE_SHA
            or binding.sha(args.resource_replay) != curvature_probe.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("cover arithmetic test changed the fixed zero-source context")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    layer = identity.gate(binding.read(args.current_audit), current_digest, args.source)
    pending = {row["index"]: row for row in binding.read(args.source / "PENDING-ANGLES.json")}
    diagnosis = binding.read(args.diagnosis)
    if (diagnosis["verified"] is not False
            or diagnosis["actual_current_audit_sha256"] != current_digest
            or diagnosis["new_geometric_payments"] != 0
            or diagnosis["modules"][linux(Path(cover.hull.__file__))] != binding.sha(cover.hull.__file__)):
        raise ValueError("cover arithmetic test lacks actual unchanged diagnosis/module identity")
    arcs = binding.force.load_trig(args.resource)[0]
    results = []
    for item in diagnosis["roots"]:
        results.append(cover.replay(
            original, kernel, arcs, pending[item["source_OPEN_index"]], item))
    first = diagnosis["roots"][0]
    row = pending[first["source_OPEN_index"]]
    rejected = []

    def reject(name, mutation):
        bad = deepcopy(first)
        mutation(bad)
        try:
            cover.replay(original, kernel, arcs, row, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(name)
        else:
            raise AssertionError("invalid hull/LOCAL cover accepted: " + name)

    reject("whole-root-ownership-index-changed",
           lambda bad: bad.update(source_OPEN_index=row["index"] + 1))
    reject("first-closed-slab-omitted",
           lambda bad: bad["sequential_closed_slabs"].pop(0))
    reject("hidden-additional-slab",
           lambda bad: bad["sequential_closed_slabs"].append(
               deepcopy(bad["sequential_closed_slabs"][0])))
    reject("shared-closed-split-boundary-lost",
           lambda bad: bad["sequential_closed_slabs"][0].update(
               both_closed_halves_include_shared_cut=False))
    reject("slab-sharp-domain-clipped",
           lambda bad: bad["sequential_closed_slabs"][0]["sharp_lower"].__setitem__(0, "0"))
    reject("central-remainder-clipped",
           lambda bad: bad["central_closed_box"]["closed_lower"].__setitem__(0, "0"))
    reject("positive-curvature-unsupported-by-exact-LDL",
           lambda bad: bad["sequential_closed_slabs"][0]["certificate"]["signed_eta"].__setitem__(10, "-1000000"))
    reject("negative-difference-dual-multiplier",
           lambda bad: bad["sequential_closed_slabs"][0]["certificate"]["difference_dual"].update(
               terms=[[0, 1, "-1"]]))
    reject("reference-outside-necessary-difference-domain",
           lambda bad: bad["sequential_closed_slabs"][0]["certificate"]["reference_turns"].__setitem__(0, "100"))
    reject("discovery-strict-result-fabricated",
           lambda bad: bad["sequential_closed_slabs"][0]["arithmetic_result"].update(
               minimum_strict_energy_margin="1"))
    reject("LOCAL-allowance-expanded",
           lambda bad: bad["central_closed_box"]["original_LOCAL_result"].update(
               original_52_coordinate_local_allowance="1"))
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("current snapshot changed during independent cover arithmetic test")
    report = {
        "schema": "N26-independent-signed-hull-LOCAL-cover-arithmetic-controls-v1",
        "all_arithmetic_cover_reconstructions_passed": True,
        "root_arithmetic_checks": results,
        "strict_signed_hull_slabs_checked": sum(
            result["strict_signed_hull_energy_slabs"] for result in results),
        "original_LOCAL_central_boxes_checked": len(results),
        "rejection_controls_passed": rejected,
        "actual_latest_candidate_layer_identity_only": layer,
        "actual_current_audit_sha256": current_digest,
        "diagnosis_sha256": binding.sha(args.diagnosis),
        "resource_acceptance_sha256": curvature_probe.RESOURCE_SHA,
        "arithmetic_only_not_a_geometric_source_or_ownership_replay": True,
        "full_source_model_history_replay_not_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_test_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (cover, cover.hull, cover.forest, codec, identity)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("root_arithmetic_checks", "modules")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
