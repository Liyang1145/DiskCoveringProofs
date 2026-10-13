"""Freeze a DISTINCT actual entire-source six-target bundle, NOT acceptance."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding
import verify_six_target_source_geometry as checker


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError("six-target builder never resets an existing frozen bundle")
    parent_path = Path("outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json")
    final_path = Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json")
    source_folder = Path("outputs/n26-conditional-force-stage-v28-sparse-v1")
    candidate_folder = Path("outputs/n26-current-candidate-owned-forest-v8")
    family_folder = Path("outputs/n26-new-scope-v1")
    producer_path = Path("outputs/n26-current28-six-target-filled-ear-mathematical-scan-v1.json")
    controls_path = Path("outputs/n26-current28-six-target-filled-ear-independent-controls-v1.json")
    parent, final = binding.read(parent_path), binding.read(final_path)
    checker.previous.parent_gate(parent, final, binding.sha(parent_path))
    producer, controls = binding.read(producer_path), binding.read(controls_path)
    if (
        producer["verified"] is not False or controls["verified"] is not False
        or producer["new_formal_geometric_payments"] != 0 or controls["new_formal_geometric_payments"] != 0
        or producer["actual_qualifying_whole_prefixes"] != 5546
        or controls["independent_qualifying_whole_prefixes"] != 5546
        or controls["entire_original_source_prefixes_independently_reconstructed"] != 11183
        or controls["independent_original_set_enumeration_cases_checked"] != 58916
    ):
        raise ValueError("six-target builder lacks actual completed complete-source mathematical controls")
    for record in (producer, controls):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("six-target actual mathematical/control dependency changed before freezing")
    data = {
        "SOURCE-CURRENT.json": parent_path, "SOURCE-FINAL.json": final_path,
        "SOURCE-FRONTIER.json": source_folder/"FRONTIER.json",
        "SOURCE-ACCEPTANCE.json": source_folder/"VERIFIED.json",
        "FAMILY-ACCEPTANCE.json": family_folder/"VERIFIED.json",
        "FAMILY-CONSTANTS.json": family_folder/"CONSTANTS.json",
        "SIX-TARGET-MATHEMATICAL-SCAN.json": producer_path,
        "SIX-TARGET-INDEPENDENT-CONTROLS.json": controls_path,
        "BRIDGE-CONTROLS.json": Path("outputs/n26-empty-circle-corner-starring-independent-controls-v1.json"),
        "UNIT-CAP-CONTROLS.json": Path("outputs/n26-universal-unit-cap-polynomial-independent-controls-v1.json"),
        "GENERIC-CONTROLS.json": Path("outputs/n26-universal-strict-slack-generic-position-independent-controls-v1.json"),
        "UNIT-CAP-CERTIFICATE.json": Path("outputs/n26-universal-unit-cap-polynomial-certificate-v1.json"),
        "GENERIC-CERTIFICATE.json": Path("outputs/n26-universal-strict-slack-generic-position-polynomial-certificate-v1.json"),
        "EMBEDDED-CORNER-CERTIFICATE.json": Path("outputs/n26-empty-circle-corner-starring-universal-algebra-v1.json"),
        "UNIT-CAP-PROOF.md": Path("work/n26-unit-cap-domination-and-no-return-proof.md"),
        "GENERIC-SLACK-PROOF.md": Path("work/n26-strict-slack-generic-position-proof.md"),
        "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md": Path("work/n26-embedded-dual-and-corner-starring-bridge-proof.md"),
        "CLOSED-EAR-PROOF.md": Path("work/n26-closed-ear-core-capacity-proof.md"),
        "SIX-CORE-TARGET-FILLED-EAR-PROOF.md": Path("work/n26-six-core-target-filled-ear-proof.md"),
    }
    copies = dict(checker.executed_modules())
    copies.update(data)
    _, trig_path = checker.transfer.force.load_trig(source_folder)
    copies["exact_arcs.py"] = Path(trig_path)
    source = binding.read(data["SOURCE-FRONTIER.json"])
    certificates = {key: binding.read(data[name]) for key, name in checker.CERTIFICATES.items()}
    proofs = {key: binding.sha(data[name]) for key, name in checker.PROOFS.items()}
    frontier, ledger, semantic = checker.transfer.partition(
        source, binding.read(data["FAMILY-CONSTANTS.json"]), certificates, proofs)
    if [row["source_index"] for row in ledger] != [row["actual_source_index"] for row in producer["results"]]:
        raise ValueError("six-target frozen whole-source ledger differs from actual independent mathematics")
    pool_path = parent_path.with_name(parent_path.stem+"-closed-type-pool.json")
    terminal_path = parent_path.with_name(parent_path.stem+"-terminal-obligations.json")
    for path in (data["SOURCE-FRONTIER.json"], data["SOURCE-ACCEPTANCE.json"], pool_path, terminal_path):
        if parent["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("six-target builder substituted actual source/type/terminal ownership")
    args.output.mkdir(parents=True)
    for name, path in copies.items():
        with (args.output/name).open("xb") as target:
            target.write(path.read_bytes())
    for name, value in (
        ("FRONTIER.json", frontier), ("LOWER-LEDGER.json", ledger),
        ("SOURCE-MATHEMATICAL-SEMANTICS.json", semantic),
    ):
        with (args.output/name).open("x", encoding="utf-8", newline="\n") as target:
            target.write(json.dumps(value, indent=2)+"\n")
    copied = {name: binding.sha(args.output/name) for name in copies}
    copied.update({name: binding.sha(args.output/name) for name in (
        "FRONTIER.json", "LOWER-LEDGER.json", "SOURCE-MATHEMATICAL-SEMANTICS.json")})
    manifest = {
        "schema": checker.INPUT_SCHEMA, "checker": checker.CHECKER,
        "rule_mode": checker.transfer.MODE, "radius_scope": binding.SCOPE,
        "parent_current": linux(parent_path), "parent_current_sha256": binding.sha(parent_path),
        "parent_final": linux(final_path), "parent_final_sha256": binding.sha(final_path),
        "source_frontier": linux(data["SOURCE-FRONTIER.json"]),
        "source_frontier_sha256": binding.sha(data["SOURCE-FRONTIER.json"]),
        "source_acceptance": linux(data["SOURCE-ACCEPTANCE.json"]),
        "source_acceptance_sha256": binding.sha(data["SOURCE-ACCEPTANCE.json"]),
        "actual_candidate_source": linux(candidate_folder), "family_scope": linux(family_folder),
        "original_rational_upper_acceptance": linux(Path("outputs/n26-rational-upper-v1/VERIFIED.json")),
        "closed_type_pool": linux(pool_path), "terminal_obligations": linux(terminal_path),
        "mathematical_scan_sha256": binding.sha(producer_path),
        "independent_controls_sha256": binding.sha(controls_path),
        "full_actual_parent_inventory_and_source_reconstruction_required": True,
        "current_adoption_is_not_done_by_own_geometry": True,
        "old643_geometry_NOT_a_substitute_for_new5546_actual_main": True,
        "candidate_roots_and_all_old_histories_UNCHANGED": True,
        "builder_only_NOT_geometry_acceptance": True, "copied_files": copied,
    }
    with (args.output/"MANIFEST.json").open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(manifest, indent=2)+"\n")
    print(json.dumps({
        "six_target_actual_source_bundle_frozen": True,
        "source_frontier": len(source["pending_states"]), "prepared_filtered_frontier": len(frontier["pending_states"]),
        "prepared_whole_prefixes": len(ledger), "actual_geometry_main_STILL_required": True,
        "new_formal_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
