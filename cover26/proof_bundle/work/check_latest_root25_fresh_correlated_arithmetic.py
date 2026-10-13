"""Independent recomputation of actual new root25 certificates, no fixture gate."""

from fractions import Fraction as F
import json
from pathlib import Path

import n26_typed_arithmetic_context as codec
import test_full134rod_correlated_support as independent
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-latest-root25-fresh-correlated-independent-arithmetic-v1.json")
    if output.exists():
        raise FileExistsError(output)
    path = Path("outputs/n26-latest-root25-fresh-correlated-stress-v1.json")
    record = binding.read(path)
    digests = dict(record["input_sha256"])
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("actual closed-domain input changed before independent recomputation")
    digests[str(path)] = binding.sha(path)
    digests[__file__] = binding.sha(__file__)
    digests[independent.__file__] = binding.sha(independent.__file__)
    resource = Path("outputs/n26-original-candidate-arithmetic-context-v1")
    original = codec.gate(binding.read(resource/"CONTEXT.json")["typed_context"])["original"]
    full = independent.full
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    arcs = binding.force.load_trig(resource)[0]
    latest_path = Path("outputs/n26-candidate-root25-checked-support-cost-forest-diagnosis-v3.json")
    latest = binding.read(latest_path)
    pending = {leaf["index"]: leaf for leaf in latest["pending_closed_leaf_boxes"]}
    summaries = []
    for item in record["results"]:
        leaf = item["actual_latest_root25_v3_OPEN_leaf"]
        if pending.get(leaf["index"]) != leaf or latest["nodes"][leaf["index"]] != {"kind": "OPEN"}:
            raise ValueError("independent arithmetic target is not the actual latest OPEN leaf")
        kernel = full.kernel_gate(model, item["fresh_full134rod_positive_stress_kernel_certificate"])
        for trial in item["trials"]:
            a, b = list(map(F, trial["closed_lower"])), list(map(F, trial["closed_upper"]))
            if any(not F(x) <= p <= q <= F(y)
                   for x, y, p, q in zip(leaf["lower"], leaf["upper"], a, b)):
                raise ValueError("proper certificate lies outside actual newest parent leaf")
            whole = a == list(map(F, leaf["lower"])) and b == list(map(F, leaf["upper"]))
            if whole != trial["is_entire_actual_latest_OPEN_leaf"]:
                raise ValueError("proper neighborhood was promoted to a whole-leaf certificate")
            certificate = trial["fresh_correlated_certificate"]
            if certificate is None:
                continue
            shape = {"lower": list(map(str, a)), "upper": list(map(str, b))}
            exact_trial = {
                "NEW_correlated_quadratic_certificate": certificate,
                "NEW_correlated_exact_closed_leaf_result": trial["fresh_correlated_result"],
            }
            result = independent.arithmetic_control(original, kernel, shape, exact_trial, arcs)
            summaries.append({
                "actual_latest_root25_leaf_index": leaf["index"], "domain": trial["domain"],
                "entire_actual_parent_leaf": whole,
                "independent_entire_closed_target_strict": result["arithmetic_strict_target_test_passed"],
                "strict_energy_margin": result["strict_energy_margin"],
                "strict_radius_margin": result["strict_radius_margin"],
                "independent_normalized_Taylor_LDL_secant_dual_and_square_completion_reconstructed": True,
                "independent_feasible_sine_square_point_checks": 3,
            })
            print(json.dumps(summaries[-1]), flush=True)
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("actual independent arithmetic inputs changed")
    report = {
        "schema": "N26-actual-latest-root25-fresh-correlated-independent-arithmetic-v1",
        "verified": False, "source_OPEN_index": 25, "input_sha256": digests, "results": summaries,
        "actual_closed_target_certificates_independently_reconstructed": len(summaries),
        "strict_whole_parent_leaves": sum(row["independent_entire_closed_target_strict"]
                                        and row["entire_actual_parent_leaf"] for row in summaries),
        "strict_proper_neighborhoods_NOT_disjoint_payments": sum(
            row["independent_entire_closed_target_strict"] and not row["entire_actual_parent_leaf"]
            for row in summaries),
        "all_actual_latest_forest_nodes_supports_ledgers_and_payments_UNMODIFIED": True,
        "complete_latest_source_geometry_replay_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
