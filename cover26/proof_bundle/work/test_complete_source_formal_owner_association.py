"""Actual current/source identity association and real preflight rejection paths.

This never calls the complete semantic model/source/history gate. It cannot
produce a geometry acceptance or payment, even if every identity guard passes.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest_candidate_complete_source_replay as adapter
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "source-replay", "formal-current", "formal-final",
                 "candidate-owner-current", "candidate-owner-final", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    paths = (args.source, args.source_replay, args.formal_current, args.formal_final,
             args.candidate_owner_current, args.candidate_owner_final)
    adapter_digest, executed_digest = binding.sha(adapter.__file__), binding.sha(__file__)
    snapshot = adapter.preflight(*paths)
    rejected = []

    def reject(label, changed=None, bad_path=None, mutation=None, bad_identity=None):
        call_paths = paths if changed is None else changed
        wrong = None if bad_path is None else binding.read(bad_path)
        if wrong is not None:
            mutation(wrong)

        def reader(path):
            if bad_path is not None and binding.local_path(path).resolve() == bad_path.resolve():
                return deepcopy(wrong)
            return binding.read(path)

        def identifier(current, digest, source, **kwargs):
            value = adapter.identity.gate(current, digest, source, **kwargs)
            if bad_identity is not None:
                bad_identity(value)
            return value

        try:
            adapter.preflight(*call_paths, reader=reader, identifier=identifier)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid complete-source identity preflight accepted: "+label)

    reject("formal-enumeration-pair-substituted-for-candidate-owner",
           changed=(*paths[:4], args.formal_current, args.formal_final))
    reject("candidate-owner-final-substituted-for-formal-final",
           changed=(args.source, args.source_replay, args.formal_current,
                    args.candidate_owner_final, *paths[4:]))
    reject("formal-final-current-hash-forged", bad_path=args.formal_final,
           mutation=lambda bad: bad.update(current_audit_sha256="0"*64))
    reject("formal-final-inventory-count-shortened", bad_path=args.formal_final,
           mutation=lambda bad: bad.update(current_file_digests_rechecked=0))
    reject("formal-final-unresolved-root-count-changed", bad_path=args.formal_final,
           mutation=lambda bad: bad.update(candidate_angle_unresolved_closed_boxes=0))
    reject("formal-final-incomplete-rehash-promoted", bad_path=args.formal_final,
           mutation=lambda bad: bad.update(all_current_file_digests_rehashed=False))
    reject("candidate-owner-final-current-hash-forged", bad_path=args.candidate_owner_final,
           mutation=lambda bad: bad.update(current_audit_sha256="0"*64))
    reject("formal-radius-scope-promoted-to-U", bad_path=args.formal_current,
           mutation=lambda bad: bad.update(radius_scope="unconditional-original-U"))
    reject("formal-LOCAL-coordinate-allowance-enlarged", bad_path=args.formal_current,
           mutation=lambda bad: bad.update(original_52_coordinate_local_allowance_unchanged="1"))
    reject("candidate-owner-final-ancestor-unbound", bad_path=args.formal_current,
           mutation=lambda bad: bad["files"].pop(linux(args.candidate_owner_final)))
    reject("actual-source-publication-unbound", bad_path=args.formal_current,
           mutation=lambda bad: bad["files"].pop(linux(args.source_replay)))
    reject("wrong-equal-count-candidate-owner-identity", bad_identity=lambda bad:
           bad.update(latest_candidate_current_audit_sha256="0"*64))
    reject("arithmetic-context-promoted-to-candidate-source-schema",
           bad_path=args.source / "VERIFIED.json", mutation=lambda bad:
           bad.update(schema="N26-original-candidate-arithmetic-context-v1"))
    reject("unaccepted-candidate-source-promoted", bad_path=args.source / "VERIFIED.json",
           mutation=lambda bad: bad.update(verified=False))
    reject("source-radius-endpoint-replaced-by-U", bad_path=args.source / "VERIFIED.json",
           mutation=lambda bad: bad.update(radius_upper="234701/1000000"))
    if (adapter.preflight(*paths) != snapshot
            or binding.sha(adapter.__file__) != adapter_digest
            or binding.sha(__file__) != executed_digest):
        raise ValueError("complete source preflight actual bytes changed during identity controls")
    report = {
        "schema": "N26-independent-distinct-formal-candidate-owner-source-association-controls-v1",
        "verified": False,
        "actual_formal_and_candidate_owner_identity_snapshot": snapshot,
        "actual_invalid_formal_owner_pair_source_scope_and_binding_controls_rejected": rejected,
        "ENTIRE_actual_source_model_history_geometry_gate_NOT_executed": True,
        "identity_controls_are_NOT_a_complete_source_replay_or_geometry_payment": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "executed_test_sha256": executed_digest,
        "tested_complete_source_adapter_sha256": adapter_digest,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_formal_and_candidate_owner_identity_controls_completed": True,
        "actual_rejections": len(rejected),
        "complete_geometry_source_gate_NOT_executed": True,
        "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
