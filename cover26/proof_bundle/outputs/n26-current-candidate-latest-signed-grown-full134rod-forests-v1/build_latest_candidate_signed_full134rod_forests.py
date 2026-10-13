"""Freeze BOTH actual newest forests; do not run a geometry or payment cache."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding
import verify_latest_candidate_signed_full134rod_forests as checker


ARGUMENTS = (
    "source", "source-replay", "formal-current", "formal-final",
    "candidate-owner-current", "candidate-owner-final", "arithmetic-proof-time-source",
    "root25-diagnosis", "root25-controls", "root25-seed",
    "root28-v8", "root28-v8-controls", "root28-grown-diagnosis", "root28-grown-controls",
    "interface-contract-controls",
    "output",
)
INPUT_COPIES = {
    "root25_diagnosis": "ROOT25-DIAGNOSIS.json",
    "root25_controls": "ROOT25-CONTROLS.json",
    "root25_seed": "ROOT25-SEED.json",
    "root28_v8": "ROOT28-V8.json",
    "root28_v8_controls": "ROOT28-V8-CONTROLS.json",
    "root28_grown_diagnosis": "ROOT28-GROWN-DIAGNOSIS.json",
    "root28_grown_controls": "ROOT28-GROWN-CONTROLS.json",
    "interface_contract_controls": "INTERFACE-CONTRACT-CONTROLS.json",
}


def main():
    parser = argparse.ArgumentParser()
    for name in ARGUMENTS:
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError("latest forest geometry needs an entirely fresh frozen bundle")
    for attribute in INPUT_COPIES:
        path = getattr(args, attribute)
        if not path.is_file():
            raise ValueError("actual newest producer AND automatic independent controls incomplete: "+str(path))
    paths = (args.source, args.source_replay, args.formal_current, args.formal_final,
             args.candidate_owner_current, args.candidate_owner_final)
    association = checker.source_backend.preflight(*paths)
    accepted, _ = binding.bound(args.source)
    proof_acceptance, _ = binding.bound(args.arithmetic_proof_time_source)
    incoming = binding.read(args.source / "PENDING-ANGLES.json")
    # This is retained history DATA only. The actual complete source gate is
    # mandatory in the frozen verifier; the builder does not execute or cache it.
    if accepted["schema"] == checker.source_backend.owned.SCHEMA:
        history, _ = checker.source_backend.owned.history(args.source, incoming)
        retained_history = [history[index] for index in sorted(history)]
    else:
        retained_history = binding.read(args.source / "REMAINING-ROOT-HISTORY.json")
    records = {25: binding.read(args.root25_diagnosis),
               28: binding.read(args.root28_grown_diagnosis)}
    controls = {25: binding.read(args.root25_controls),
                28: binding.read(args.root28_grown_controls)}
    seeds = {25: binding.read(args.root25_seed), 28: binding.read(args.root28_v8)}
    checker.root_gate(incoming, records)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend((path, name) for name, path in checker.executed_modules().items())
    copies.extend((getattr(args, attribute), name) for attribute, name in INPUT_COPIES.items())
    copies.extend((
        (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
        (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
        (args.formal_current, "SOURCE-CURRENT-AUDIT.json"),
        (args.formal_final, "SOURCE-FINAL-DIGEST-RECHECK.json"),
        (args.candidate_owner_current, "SOURCE-OWNER-CURRENT.json"),
        (args.candidate_owner_final, "SOURCE-OWNER-FINAL.json"),
        (args.arithmetic_proof_time_source / "VERIFIED.json", "PROOF-SOURCE-ACCEPTANCE.json"),
        (Path(__file__).with_name("n26-latest-signed-grown-full134rod-geometry-admission-proof.md"),
         "PROOF.md"),
        (Path(__file__).with_name("test_latest_signed_full134_geometry_contracts.py"),
         "test_latest_signed_full134_geometry_contracts.py"),
    ))
    module_digests = {}
    for record in (*records.values(), *seeds.values()):
        for text, digest in record["modules"].items():
            name = binding.local_path(text).name
            if name in module_digests and module_digests[name] != digest:
                raise ValueError("latest reports bind incompatible code under one frozen file name")
            module_digests[name] = digest
    for control in controls.values():
        for name, digest in control["tested_modules"].items():
            if name in module_digests and module_digests[name] != digest:
                raise ValueError("actual newest independent controls tested different arithmetic")
            module_digests[name] = digest
    for name, digest in module_digests.items():
        path = Path(__file__).with_name(name)
        if binding.sha(path) != digest:
            raise ValueError("a diagnostic/test executor changed since its actual independent controls")
        copies.append((path, name))
    for name in (*checker.PRODUCERS.values(), *checker.TESTERS.values()):
        copies.append((Path(__file__).with_name(name), name))
    planned = {}
    for path, name in copies:
        digest = binding.sha(path)
        if name in planned and binding.sha(planned[name]) != digest:
            raise ValueError("different sealed source and new arithmetic versions collide: "+name)
        planned[name] = path
    expected = {name: binding.sha(path) for name, path in planned.items()}
    checker.records_gate(
        records, controls, seeds, expected, expected, incoming)
    for record in (*records.values(), *seeds.values()):
        for name, digest in record["source_file_sha256"].items():
            if (proof_acceptance["files"].get(name) != digest
                    or binding.sha(args.arithmetic_proof_time_source / name) != digest):
                raise ValueError("actual newest forest source/history DATA changed before freezing")
    args.output.mkdir(parents=True)
    for name, path in planned.items():
        with (args.output / name).open("xb") as output:
            output.write(path.read_bytes())
    with (args.output / "SOURCE-ROOT-HISTORY.json").open(
            "x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(retained_history, indent=2)+"\n")
    manifest = {
        "schema": checker.INPUT_SCHEMA, "radius_scope": "same-root-Rstar",
        "acceptance_checker_file": checker.CHECKER,
        "supported_forest_modes": checker.MODES,
        "complete_latest_source_model_history_replay_required": True,
        "typed_resource_not_a_source_replay_substitute": True,
        "latest_grown_v9_and_root25_v3_NOT_reset": True,
        "source": linux(args.source), "source_replay": linux(args.source_replay),
        "source_acceptance_sha256": binding.sha(args.source / "VERIFIED.json"),
        "arithmetic_proof_time_source": linux(args.arithmetic_proof_time_source),
        "proof_time_source_acceptance_sha256": binding.sha(
            args.arithmetic_proof_time_source / "VERIFIED.json"),
        "actual_preflight_identity_only": association,
        "copied_files": {name: binding.sha(args.output / name)
                         for name in (*planned, "SOURCE-ROOT-HISTORY.json")},
        "verified": False, "new_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    for name in ("formal_current", "formal_final", "candidate_owner_current", "candidate_owner_final"):
        path = getattr(args, name)
        manifest[name], manifest[name+"_sha256"] = linux(path), binding.sha(path)
    with (args.output / "MANIFEST.json").open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(manifest, indent=2)+"\n")
    checker.metadata_gate(args.output)
    print(json.dumps({
        "both_actual_latest_forests_frozen": True,
        "verified": False, "new_geometric_payments": 0,
        "COMPLETE_original_latest_model_source_history_geometry_acceptance_still_required": True,
    }), flush=True)


if __name__ == "__main__":
    main()
