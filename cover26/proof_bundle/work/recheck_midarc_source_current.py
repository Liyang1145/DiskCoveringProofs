"""Independent REAL final for NEW680 midarc enumeration current.

Own hashing/path normalization, complete ORIGINAL5637-prefix reconstruction,
independent whole ledger/frontier accounting, actual full-main command and
all original candidate/type/receipt/history bindings are required.
"""

import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys

from audit_prefix_origin import OriginReference
import n26_force as force
import n26_candidate_identity_after_midarc as identity
import n26_midarc_current_accounting as accounting


def local_path(value):
    text = str(value).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper() + ":" + text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/" + text[0].lower() + text[2:])
    return Path(text)


def sha(path):
    digest = hashlib.sha256()
    with local_path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024*1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "geometry", "geometry-replay", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("independent midarc final never overwrites reports")
    initial = sha(args.current_audit)
    current = read(args.current_audit)
    if current["schema"] != accounting.CURRENT_SCHEMA:
        raise ValueError("midarc final cannot certify older SIX/native/mixed-admission schemas")
    inventory = current["files"]
    normalized = {str(local_path(text).resolve()): value for text, value in inventory.items()}
    if len(normalized) != len(inventory):
        raise ValueError("midarc final has duplicate normalized bound paths")

    def bound(path):
        if normalized.get(str(local_path(path).resolve())) != sha(path):
            raise ValueError("midarc final input/executor not bound: " + str(path))

    for number, (text, digest) in enumerate(inventory.items(), 1):
        if sha(text) != digest:
            raise ValueError("midarc final bound dependency changed: " + text)
        if number % 10000 == 0:
            print(json.dumps({
                "midarc_final_inventory_rehashed": number, "total": len(inventory),
            }), flush=True)
    parent_path = local_path(current["midarc_parent_audit_file"])
    final_path = local_path(current["midarc_parent_final_file"])
    bound(parent_path)
    bound(final_path)
    parent, parent_final = read(parent_path), read(final_path)
    parent_digest, final_digest = sha(parent_path), sha(final_path)
    accounting.source.parent_gate(parent, parent_final, parent_digest)
    if (
        parent_digest != current["prior_current_audit_sha256"]
        or final_digest != current["midarc_parent_final_sha256"]
        or current["prior_current_file_digests_rechecked"] != len(parent["files"])
    ):
        raise ValueError("midarc final lost actual completed mixed16-root parent pair")
    final_executor = Path(__file__).with_name("recheck_mixed_curvature_candidate_after_six_current.py")
    bound(final_executor)
    if parent_final["executed_checker_sha256"] != sha(final_executor):
        raise ValueError("midarc final lacks actual completed parent independent final executor")
    if (
        local_path(current["midarc_geometry_folder"]).resolve() != args.geometry.resolve()
        or local_path(current["midarc_geometry_publication_file"]).resolve() != args.geometry_replay.resolve()
        or local_path(current["current_frontier_actual_file"]).resolve()
        != (args.geometry / "FRONTIER.json").resolve()
    ):
        raise ValueError("midarc final received a different actual geometry/frontier/publication")
    manifest = read(args.geometry / "MANIFEST.json")
    source_path = local_path(manifest["source_frontier"])
    if (
        manifest["parent_current_sha256"] != parent_digest or manifest["parent_final_sha256"] != final_digest
        or local_path(manifest["parent_current"]).resolve() != parent_path.resolve()
        or local_path(manifest["parent_final"]).resolve() != final_path.resolve()
        or sha(source_path) != manifest["source_frontier_sha256"]
        or read(source_path) != read(args.geometry / "SOURCE-FRONTIER.json")
        or local_path(parent["current_frontier_actual_file"]).resolve() != source_path.resolve()
    ):
        raise ValueError("midarc final substituted actual original source or proof-time parent")
    source, frontier = read(source_path), read(args.geometry / "FRONTIER.json")
    ledger = read(args.geometry / "LOWER-LEDGER.json")
    constants = read(args.geometry / "FAMILY-CONSTANTS.json")
    proofs = {key: sha(args.geometry / name) for key, name in {
        "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
        "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
        "midarc": "MIDARC-SEVEN-SIX-FIVE-TARGET-PROOF.md",
    }.items()}
    candidate = local_path(manifest["actual_candidate_source"])
    layer = identity.previous.gate(parent, parent_digest, candidate, reader=read, hasher=sha)
    accepted = read(args.geometry / "VERIFIED.json")
    semantic_path = local_path(current["midarc_geometry_semantic_replay_file"])
    checker_path = args.geometry / accounting.CHECKER
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, read(args.geometry_replay),
        read(semantic_path), sha(checker_path), layer,
    )
    command = current["midarc_full_current_semantic_command"]
    expected = [
        sys.executable, str(checker_path), "--input", str(args.geometry),
        "--report", str(semantic_path),
    ]
    if (
        sha(args.geometry / "VERIFIED.json") != sha(args.geometry_replay)
        or sha(args.geometry / "VERIFIED.json") != sha(semantic_path)
        or accepted["actual_source_frontier_sha256"] != sha(source_path)
        or len(command) != 6 or command[2] != "--input" or command[4] != "--report"
        or [str(local_path(command[index]).resolve()) for index in (0, 1, 3, 5)]
        != [str(local_path(expected[index]).resolve()) for index in (0, 1, 3, 5)]
    ):
        raise ValueError("midarc final lacks actual byte-identical triple and full frozen-main execution command")
    references = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
                  for b in (14, 15, 16, 17)}
    for reference in references.values():
        reference.children = lru_cache(None)(reference.children)
    for number, row in enumerate(source["pending_states"], 1):
        reference = references[row["B"]]
        prefix = tuple(row["prefix"])
        state = reference.resolve(prefix)
        if {"B": row["B"], **reference.entry(prefix, state, reference.children(state))} != row:
            raise ValueError("midarc independent final ENTIRE ORIGINAL prefix reconstruction differs")
        if number % 1000 == 0:
            print(json.dumps({
                "midarc_final_ORIGINAL_source_prefixes_reconstructed": number,
                "total": len(source["pending_states"]),
            }), flush=True)
    result = accounting.source.partition_gate(source, frontier, ledger, constants, proofs)
    accounting.current_gate(current, parent, result, layer)
    if result != accepted["independent_complete_actual_remaining_source_accounting"]:
        raise ValueError("midarc real geometry differs from independent full-current ledger accounting")
    result_identity = identity.gate(current, initial, candidate, reader=read, hasher=sha)
    if result_identity["actual_remaining_candidate_whole_roots"] != 16:
        raise ValueError("midarc final did not preserve exact actual16-root candidate owner")
    for text, digest in accepted["source_files"].items():
        if normalized.get(str(local_path(text).resolve())) != digest:
            raise ValueError("midarc current lost/changed a whole-geometry source proof dependency")
    for name, digest in accepted["files"].items():
        if normalized.get(str((args.geometry / name).resolve())) != digest:
            raise ValueError("midarc current omitted a frozen actual code/proof/source/ledger")
        bound(args.geometry / name)
    for suffix in ("-closed-type-pool.json", "-closed-receipt-checks.json", "-terminal-obligations.json"):
        new_path = args.current_audit.with_name(args.current_audit.stem + suffix)
        old_path = parent_path.with_name(parent_path.stem + suffix)
        bound(new_path)
        bound(old_path)
        if sha(new_path) != sha(old_path):
            raise ValueError("midarc final changed an original type/receipt/raw terminal sidecar")
    pool = read(args.current_audit.with_name(args.current_audit.stem + "-closed-type-pool.json"))
    receipts = read(args.current_audit.with_name(args.current_audit.stem + "-closed-receipt-checks.json"))
    obligations = read(args.current_audit.with_name(args.current_audit.stem + "-terminal-obligations.json"))
    if (
        len(pool) != 87 or len(receipts) != 215
        or obligations != parent["all_current_competitor_terminal_obligations_explicitly_retained"]
        or obligations != current["all_current_competitor_terminal_obligations_explicitly_retained"]
    ):
        raise ValueError("midarc final lost old full-type/proof-receipt/raw terminal closure")
    executor_path = local_path(current["midarc_current_admission_executor_file"])
    if (
        executor_path.resolve() != Path(__file__).with_name("audit_midarc_source_current.py").resolve()
        or current["midarc_current_admission_executor_sha256"] != sha(executor_path)
        or local_path(current["midarc_identity_adapter_file"]).resolve() != Path(identity.__file__).resolve()
        or current["midarc_identity_adapter_sha256"] != sha(identity.__file__)
    ):
        raise ValueError("midarc final relabelled actual new compositor or explicit candidate adapter")
    work = Path(__file__).resolve().parent
    for module in list(sys.modules.values()):
        text = getattr(module, "__file__", None)
        if text:
            path = Path(text).resolve()
            if path.suffix == ".py" and path.parent == work:
                bound(path)
    for path in (
        __file__, executor_path, source_path, semantic_path,
        args.geometry / "VERIFIED.json", args.geometry_replay,
        candidate / "VERIFIED.json", candidate / "PENDING-ANGLES.json",
        candidate / "REMAINING-ROOT-HISTORY.json",
    ):
        bound(path)
    if sha(args.current_audit) != initial or sha(parent_path) != parent_digest or sha(final_path) != final_digest:
        raise ValueError("midarc actual current/parent changed during independent final semantics")
    report = {
        "schema": accounting.FINAL_SCHEMA, "all_current_file_digests_rehashed": True,
        "current_file_digests_rechecked": len(inventory), "current_audit_sha256": initial,
        "actual_own_publication_AND_complete_current_semantic_reports_byte_identical": True,
        "independent_complete_ORIGINAL_source_prefix_reconstruction": len(source["pending_states"]),
        "independent_exact_NEW_midarc_source_accounting": result,
        "actual_preserved_candidate_source_identity": result_identity,
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "new_strict_whole_prefixes": len(ledger), "candidate_whole_roots_removed": 0,
        "candidate_angle_unresolved_closed_boxes": 16,
        "all_actual16_candidate_roots_histories_and_raw_terminal_obligations_retained": True,
        "retained_closed_full_type_codes": 87, "retained_checked_proof_receipts": 215,
        "radius_scope": accounting.source.SCOPE, "r_strict_interval": current["r_strict_interval"],
        "original_U_frontier_nodes_removed": 0, "original_LOCAL_unchanged": "7/800000",
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "executed_checker_sha256": sha(__file__),
        "executed_independent_accounting_sha256": sha(accounting.source.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key not in (
        "Rstar_conditional_frontier_families", "independent_exact_NEW_midarc_source_accounting",
        "actual_preserved_candidate_source_identity",
    )}), flush=True)


if __name__ == "__main__":
    main()
