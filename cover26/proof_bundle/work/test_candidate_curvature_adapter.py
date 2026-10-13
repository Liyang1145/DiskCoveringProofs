"""Kernel regression controls, not source-angle or global acceptance."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import n26_candidate_curvature_energy as candidate
import verify_dirichlet_candidate_overlay as old
from verify_conditional_force_stage import read, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--kernel", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    reference, certificate = read(args.reference), read(args.kernel)
    kernel = candidate.kernel_gate(reference, certificate)
    positive = old.identity_control(kernel)
    rejected = []

    def reject(label, ref, cert):
        try:
            candidate.kernel_gate(ref, cert)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid original candidate energy kernel accepted: " + label)

    bad = deepcopy(certificate)
    bad["schema"] = "N26-full-type-positive-quadratic-ground-kernel-v1"
    reject("full-type-kernel-relabelled-as-candidate", reference, bad)
    bad = deepcopy(certificate)
    bad["anchor_vertices"] = 15
    reject("changed-candidate-anchor-count", reference, bad)
    bad = deepcopy(certificate)
    bad["inverse_numerators"][0][0] = str(int(bad["inverse_numerators"][0][0]) + 1)
    reject("changed-original-ground-inverse", reference, bad)
    bad = deepcopy(reference)
    bad["weight_numerators"][0] = "0"
    reject("nonpositive-original-rod-weight", bad, certificate)
    bad = deepcopy(reference)
    bad["rational_scale"] = "-1"
    reject("negative-original-weight-scale", bad, certificate)
    bad = deepcopy(reference)
    bad["edges"].append([0, 16])
    reject("extra-full-type-or-future-rod-added", bad, certificate)
    bad = deepcopy(reference)
    bad["radius_scope"] = "unconditional-U"
    reject("candidate-radius-scope-promoted-to-U", bad, certificate)
    report = {"schema": "N26-original-candidate-curvature-adapter-regression-evidence-v1",
              "original_92_rod_two_coordinate_energy_identity": positive,
              "invalid_kernel_controls_rejected": rejected,
              "current_candidate_boxes_removed_by_this_test": 0,
              "actual_source_angle_partition_and_whole_box_acceptance_still_required": True,
              "global_lower_bound_proved": False, "global_optimality_proved": False,
              "reference_sha256": sha(args.reference), "kernel_sha256": sha(args.kernel),
              "tested_adapter_sha256": sha(candidate.__file__), "executed_test_sha256": sha(__file__)}
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
