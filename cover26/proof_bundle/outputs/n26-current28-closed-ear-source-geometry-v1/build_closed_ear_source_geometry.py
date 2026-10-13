"""Freeze actual current28 ear geometry inputs; builder is NOT an acceptance."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding
import verify_closed_ear_source_geometry as checker


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError("closed-ear geometry never resets a frozen bundle")
    parent_path = Path("outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json")
    final_path = Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json")
    source_folder = Path("outputs/n26-conditional-force-stage-v28-sparse-v1")
    candidate_folder = Path("outputs/n26-current-candidate-owned-forest-v8")
    family_folder = Path("outputs/n26-new-scope-v1")
    parent, final = binding.read(parent_path), binding.read(final_path)
    checker.parent_gate(parent, final, binding.sha(parent_path))
    source = binding.read(source_folder/"FRONTIER.json")
    controls_path = Path("outputs/n26-current28-closed-ear-original-owner-shadow-transfer-controls-v1.json")
    controls = binding.read(controls_path)
    if (controls["not_an_actual_geometry_acceptance_or_current_adoption"] is not True
            or controls["new_geometric_payments"] != 0
            or controls["actual_source_mathematical_result"]["closed_ear_whole_prefixes"] != 643):
        raise ValueError("missing the actual completed ALL-source mathematical controls")
    for text, digest in controls["input_sha256"].items():
        if binding.sha(binding.local_path(text)) != digest:
            raise ValueError("actual mathematical controls changed before freezing")
    copies = {name: path for name, path in checker.executed_modules().items()}
    data = {
        "SOURCE-CURRENT.json": parent_path, "SOURCE-FINAL.json": final_path,
        "SOURCE-FRONTIER.json": source_folder/"FRONTIER.json",
        "SOURCE-ACCEPTANCE.json": source_folder/"VERIFIED.json",
        "FAMILY-ACCEPTANCE.json": family_folder/"VERIFIED.json",
        "FAMILY-CONSTANTS.json": family_folder/"CONSTANTS.json",
        "TRANSFER-CONTROLS.json": controls_path,
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
    }
    copies.update(data)
    _, trig_path = checker.transfer.force.load_trig(source_folder)
    copies["exact_arcs.py"] = Path(trig_path)
    certificates = {key: binding.read(data[name]) for key, name in checker.CERTIFICATES.items()}
    proofs = {key: binding.sha(data[name]) for key, name in checker.PROOFS.items()}
    frontier, ledger, semantics = checker.transfer.partition(
        source, binding.read(family_folder/"CONSTANTS.json"), certificates, proofs)
    pool_path = parent_path.with_name(parent_path.stem+"-closed-type-pool.json")
    terminal_path = parent_path.with_name(parent_path.stem+"-terminal-obligations.json")
    for path in (source_folder/"FRONTIER.json", source_folder/"VERIFIED.json", pool_path, terminal_path):
        if parent["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("builder changed the actual parent source/pool/terminal ownership")
    args.output.mkdir(parents=True)
    for name, path in copies.items():
        with (args.output/name).open("xb") as target:
            target.write(path.read_bytes())
    for name, value in (
        ("FRONTIER.json", frontier), ("LOWER-LEDGER.json", ledger),
        ("SOURCE-MATHEMATICAL-SEMANTICS.json", semantics),
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
        "source_frontier": linux(source_folder/"FRONTIER.json"),
        "source_frontier_sha256": binding.sha(source_folder/"FRONTIER.json"),
        "source_acceptance": linux(source_folder/"VERIFIED.json"),
        "source_acceptance_sha256": binding.sha(source_folder/"VERIFIED.json"),
        "actual_candidate_source": linux(candidate_folder),
        "family_scope": linux(family_folder),
        "original_rational_upper_acceptance": linux(Path("outputs/n26-rational-upper-v1/VERIFIED.json")),
        "closed_type_pool": linux(pool_path), "terminal_obligations": linux(terminal_path),
        "full_actual_parent_inventory_and_source_reconstruction_required": True,
        "current_adoption_is_not_done_by_own_geometry": True,
        "candidate_roots_and_all_old_histories_UNCHANGED": True,
        "builder_only_NOT_geometry_acceptance": True,
        "copied_files": copied,
    }
    with (args.output/"MANIFEST.json").open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(manifest, indent=2)+"\n")
    print(json.dumps({
        "closed_ear_ACTUAL_source_bundle_frozen": True,
        "source_frontier": len(source["pending_states"]), "prepared_filtered_frontier": len(frontier["pending_states"]),
        "prepared_whole_prefixes": len(ledger), "actual_geometry_main_STILL_required": True,
        "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
