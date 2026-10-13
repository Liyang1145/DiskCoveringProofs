"""Unaccepted lossless original arithmetic context after full legacy replay.

This exports a fixed mathematical resource, NOT a replacement current candidate
layer. All current root/seed ownership remains with the actually accepted source.
Independent capsule acceptance is still required before any faster interface.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_owned_candidate_source as source
import n26_typed_arithmetic_context as codec
import verify_candidate_curvature_overlay as original_checker
import verify_conditional_force_stage as binding


def project(values):
    original = values[3]
    data = original["data"][:5]
    if len(data) != 5 or F(data[4]["unrestricted_center_neighbourhood_halfwidth_before_rotation"]) != F(7, 800000):
        raise ValueError("original arithmetic context changed its original local barrier")
    if (
        len(original["matrix"]) != 16
        or len(original["reference"]["edges"]) != 92
        or values[5]["B"] != 16 or values[5]["vertices"] != 62
        or values[5]["original_candidate_92_rod_46_free_vertex_kernel"] is not True
    ):
        raise ValueError("original arithmetic context is not the original candidate frame")
    return {
        "original": {**{key: original[key] for key in ("cap", "reference", "matrix", "radius")},
                     "data": tuple(data)},
        "original_curvature_source_acceptance": values[2],
        "original_kernel": values[5],
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "current-audit", "current-digest-recheck", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    initial_current_sha = binding.sha(args.current_audit)
    accepted, values, pending, paths, _ = source.gate(
        args.source, args.source_replay, args.current_audit, args.current_digest_recheck
    )
    model = project(values)
    encoded = codec.pack(model)
    if codec.pack(codec.gate(encoded)) != encoded:
        raise ValueError("actual original arithmetic context did not encode losslessly")
    positive = original_checker.tiny_control(values)
    paths.extend((args.source / "VERIFIED.json", args.source_replay, args.current_audit,
                  args.current_digest_recheck, Path(__file__), Path(codec.__file__),
                  Path(original_checker.__file__)))
    # All semantic source gates above ran unchanged. Only the final byte pass is
    # deduplicated by actual path; no mathematical or geometric replay is skipped.
    distinct_paths = {linux(path): path for path in paths}
    inventory = {text: binding.sha(path) for text, path in distinct_paths.items()}
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("original arithmetic context source changed during final binding: " + text)
    if binding.sha(args.current_audit) != initial_current_sha:
        raise ValueError("original arithmetic source checkpoint changed during full semantic export")
    report = {
        "schema": "N26-unaccepted-original-candidate-arithmetic-context-export-v1",
        "verified": False, "resource_scope": "original-candidate-92-rods-same-root-Rstar",
        "source": linux(args.source), "source_replay": linux(args.source_replay),
        "source_acceptance_sha256": binding.sha(args.source / "VERIFIED.json"),
        "source_current_audit": linux(args.current_audit),
        "source_current_audit_sha256": initial_current_sha,
        "source_final_digest_recheck": linux(args.current_digest_recheck),
        "source_final_digest_recheck_sha256": binding.sha(args.current_digest_recheck),
        "all_legacy_source_geometry_and_prior_payments_replayed_by_unchanged_gate": True,
        "typed_context": encoded, "original_tiny_box_positive_control": positive,
        "source_checkpoint_remaining_whole_roots": len(pending),
        "source_checkpoint_pending_rows_sha256": binding.sha(args.source / "PENDING-ANGLES.json"),
        "context_is_not_a_current_candidate_source_or_a_seed_history_substitute": True,
        "independent_resource_acceptance_and_actual_replay_still_required": True,
        "new_geometric_candidate_payments": 0,
        "current_candidate_roots_removed": 0,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "files": inventory, "executed_producer_sha256": binding.sha(__file__),
    }
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("typed_context", "files", "original_tiny_box_positive_control")},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()
