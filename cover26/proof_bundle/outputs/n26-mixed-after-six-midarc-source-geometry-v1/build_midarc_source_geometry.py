"""Freeze DISTINCT NEW680 source geometry only from the REAL completed16-root pair.

No frozen geometry acceptance or synthetic current header is created here.
The actual complete own main and its same-main publication remain required.
"""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding
import verify_midarc_source_geometry as checker


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-current", "parent-final", "candidate-source",
                 "candidate-publication", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError("midarc builder never resets an existing frozen or partial bundle")
    parent_digest, final_digest = binding.sha(args.parent_current), binding.sha(args.parent_final)
    parent, final = binding.read(args.parent_current), binding.read(args.parent_final)
    checker.accounting.parent_gate(parent, final, parent_digest)
    source_path = binding.local_path(parent["current_frontier_actual_file"])
    source_folder = source_path.parent
    source_acceptance = source_folder / "VERIFIED.json"
    source = binding.read(source_path)
    if (
        source["schema"] != checker.accounting.SOURCE_SCHEMA
        or len(source["pending_states"]) != 5637
        or source["families"] != parent["Rstar_conditional_frontier_families"]
        or parent["files"].get(linux(source_path)) != binding.sha(source_path)
        or parent["files"].get(linux(source_acceptance)) != binding.sha(source_acceptance)
        or binding.read(source_acceptance)["files"]["FRONTIER.json"] != binding.sha(source_path)
    ):
        raise ValueError("midarc builder must use the actual completed parent's SIX-filtered source")
    layer = checker.identity.gate(parent, parent_digest, args.candidate_source)
    if (
        layer["actual_remaining_candidate_whole_roots"] != 16
        or binding.read(args.candidate_publication) != binding.read(args.candidate_source / "VERIFIED.json")
        or parent["files"].get(linux(args.candidate_publication)) != binding.sha(args.candidate_publication)
    ):
        raise ValueError("midarc builder changed actual16root candidate/publication ownership")
    producer_path = Path("outputs/n26-current28-midarc-filled-patches-mathematical-scan-v1.json")
    controls_path = Path("outputs/n26-current28-midarc-filled-patches-independent-controls-v1.json")
    remaining_path = Path("outputs/n26-midarc-SIX-filtered-source-accounting-controls-v1.json")
    producer, controls, remaining = (
        binding.read(path) for path in (producer_path, controls_path, remaining_path)
    )
    if (
        any(record["verified"] is not False for record in (producer, controls, remaining))
        or any(record["new_formal_geometric_payments"] != 0 for record in (producer, controls, remaining))
        or producer["qualifying_whole_prefixes"] != 6226
        or controls["independent_qualifying_whole_prefixes"] != 6226
        or controls["independent_all_original_count_AND_shadow_label_cases_checked"] != 68088
        or remaining["actual_SIX_filtered_frontier_sha256"] != binding.sha(source_path)
        or remaining["tested_transfer_sha256"] != binding.sha(checker.transfer.__file__)
        or remaining["tested_accounting_sha256"] != binding.sha(checker.accounting.__file__)
        or remaining["actual_independent_NEW680_source_partition"]["strict_NEW_midarc_whole_prefixes"] != 680
        or len(remaining["invalid_controls_rejected"]) != 21
    ):
        raise ValueError("midarc builder lacks actual independently completed whole/remaining source controls")
    for record in (producer, controls, remaining):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("midarc mathematics/source/control provenance changed before freezing")
    family_folder = Path("outputs/n26-new-scope-v1")
    data = {
        "SOURCE-CURRENT.json": args.parent_current, "SOURCE-FINAL.json": args.parent_final,
        "SOURCE-FRONTIER.json": source_path, "SOURCE-ACCEPTANCE.json": source_acceptance,
        "FAMILY-ACCEPTANCE.json": family_folder / "VERIFIED.json",
        "FAMILY-CONSTANTS.json": family_folder / "CONSTANTS.json",
        "MIDARC-MATHEMATICAL-SCAN.json": producer_path,
        "MIDARC-INDEPENDENT-CONTROLS.json": controls_path,
        "REMAINING-SOURCE-ACCOUNTING-CONTROLS.json": remaining_path,
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
        "MIDARC-SEVEN-SIX-FIVE-TARGET-PROOF.md": Path("work/n26-midarc-seven-and-six-target-filled-patch-proof.md"),
        "test_midarc_SIX_filtered_source_accounting.py": Path(
            "work/test_midarc_SIX_filtered_source_accounting.py"),
        "build_midarc_source_geometry.py": Path(__file__),
        "run_midarc_source_geometry_serial_pair_v1.ps1": Path("work/run_midarc_source_geometry_serial_pair_v1.ps1"),
        "run_midarc_source_geometry_after_live_mixed_chain_v1.ps1": Path(
            "work/run_midarc_source_geometry_after_live_mixed_chain_v1.ps1"),
        "MIDARC-SOURCE-ADMISSION-PROOF.md": Path("work/n26-midarc-source-geometry-admission-proof.md"),
    }
    copies = dict(checker.executed_modules())
    copies.update(data)
    _, trig_path = checker.transfer.force.load_trig(source_folder)
    copies["exact_arcs.py"] = Path(trig_path)
    certificates = {key: binding.read(data[name]) for key, name in checker.CERTIFICATES.items()}
    proofs = {key: binding.sha(data[name]) for key, name in checker.PROOFS.items()}
    frontier, ledger, semantic = checker.transfer.partition(
        source, binding.read(data["FAMILY-CONSTANTS.json"]), certificates, proofs,
    )
    independent = checker.accounting.partition_gate(
        source, frontier, ledger, binding.read(data["FAMILY-CONSTANTS.json"]), proofs,
    )
    if independent != remaining["actual_independent_NEW680_source_partition"]:
        raise ValueError("midarc prepared body differs from actually completed independent source controls")
    original_path = Path("outputs/n26-conditional-force-stage-v28-sparse-v1/FRONTIER.json")
    original = binding.read(original_path)
    expected = {
        (original["pending_states"][index]["B"], tuple(original["pending_states"][index]["prefix"]))
        for index in producer["additional_beyond_frozen_six_actual_source_indices"]
    }
    if {(row["B"], tuple(row["prefix"])) for row in ledger} != expected:
        raise ValueError("midarc builder must pay actual remaining680, not all6226 or old5546")
    suffixes = ("-closed-type-pool.json", "-closed-receipt-checks.json", "-terminal-obligations.json")
    pool_path, receipt_path, terminal_path = (
        args.parent_current.with_name(args.parent_current.stem + suffix) for suffix in suffixes
    )
    final_executor = Path("work/recheck_mixed_curvature_candidate_after_six_current.py")
    for path in (source_path, source_acceptance, pool_path, receipt_path, terminal_path, final_executor):
        if parent["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("midarc builder lost actual source/type/receipt/terminal/final binding")
    if (
        final["executed_checker_sha256"] != binding.sha(final_executor)
        or binding.sha(args.parent_current) != parent_digest
        or binding.sha(args.parent_final) != final_digest
    ):
        raise ValueError("midarc builder actual current/final snapshot changed")
    args.output.mkdir(parents=True)
    for name, path in copies.items():
        with (args.output / name).open("xb") as target:
            target.write(path.read_bytes())
    for name, value in (
        ("FRONTIER.json", frontier), ("LOWER-LEDGER.json", ledger),
        ("SOURCE-MATHEMATICAL-SEMANTICS.json", semantic),
    ):
        with (args.output / name).open("x", encoding="utf-8", newline="\n") as target:
            target.write(json.dumps(value, indent=2) + "\n")
    copied = {name: binding.sha(args.output / name) for name in copies}
    copied.update({name: binding.sha(args.output / name) for name in (
        "FRONTIER.json", "LOWER-LEDGER.json", "SOURCE-MATHEMATICAL-SEMANTICS.json",
    )})
    manifest = {
        "schema": checker.INPUT_SCHEMA, "checker": checker.CHECKER,
        "rule_mode": checker.transfer.MODE, "radius_scope": checker.accounting.SCOPE,
        "parent_current": linux(args.parent_current), "parent_current_sha256": parent_digest,
        "parent_final": linux(args.parent_final), "parent_final_sha256": final_digest,
        "actual_parent_final_executor": linux(final_executor),
        "source_frontier": linux(source_path), "source_frontier_sha256": binding.sha(source_path),
        "source_acceptance": linux(source_acceptance), "source_acceptance_sha256": binding.sha(source_acceptance),
        "actual_candidate_source": linux(args.candidate_source),
        "actual_candidate_publication": linux(args.candidate_publication),
        "actual_candidate_layer_identity": layer,
        "family_scope": linux(family_folder),
        "original_rational_upper_acceptance": linux(Path("outputs/n26-rational-upper-v1/VERIFIED.json")),
        "closed_type_pool": linux(pool_path), "closed_receipt_checks": linux(receipt_path),
        "terminal_obligations": linux(terminal_path),
        "mathematical_scan_sha256": binding.sha(producer_path),
        "independent_controls_sha256": binding.sha(controls_path),
        "remaining_source_controls_sha256": binding.sha(remaining_path),
        "full_actual_parent_inventory_and_source_reconstruction_required": True,
        "current_adoption_is_not_done_by_own_geometry": True,
        "only_actual_remaining680_NOT_repaying_old5546": True,
        "actual_mixed16root_owner_and_newest_histories_REQUIRED": True,
        "builder_only_NOT_geometry_acceptance": True, "copied_files": copied,
    }
    with (args.output / "MANIFEST.json").open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(manifest, indent=2) + "\n")
    checker.input_gate(args.output)
    checker.controls_gate(args.output, source, manifest)
    print(json.dumps({
        "actual_parent16root_midarc_source_bundle_frozen_NOT_acceptance": True,
        "source_frontier": 5637, "prepared_NEW_prefixes": 680,
        "prepared_filtered_frontier": 4957, "candidate_whole_roots_removed": 0,
        "actual_geometry_own_and_same_main_publication_STILL_required": True,
        "new_formal_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
