"""Bind current bytes and replay the root/geometry, retaining the earlier scope."""

import argparse
import importlib.util
import json
from pathlib import Path

from audit_prefix_partition import WORK
from new_upper_scope import sha as original_sha


def sha(path):
    return original_sha(str(path).replace("\\", "/"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = WORK.parent / "outputs"
    folder = out / "n26-same-root-cover-v2"
    replay_folder = out / "n26-same-root-cover-published-replay-v1"
    old_audit_path = out / "n26-new-upper-current-bundle-audit-v3.json"
    old_audit = json.loads(old_audit_path.read_text())
    for name, digest in old_audit["files"].items():
        if sha(name) != digest:
            raise ValueError("earlier current-scope input changed: " + name)
    if not old_audit["current_bound_bytes_rechecked"] or not old_audit["closed_unit_disk_upper_replayed"]:
        raise ValueError("earlier independent arithmetic/cover audit missing")
    reports = []
    inventory = [Path(__file__), old_audit_path, out / "n26-STATUS.md",
                 out / "n26-same-root-milestone-20261009.md"]
    for bundle in (folder, replay_folder):
        report_path = bundle / "VERIFIED.json"
        report = json.loads(report_path.read_text())
        if not report["verified"] or report["global_optimality_proved"] or report["local_optimality_proved"]:
            raise ValueError("wrong geometric acceptance scope")
        for name, digest in report["files"].items():
            path = bundle / name
            if path.parent != bundle or sha(path) != digest:
                raise ValueError("changed published input: " + str(path))
            inventory.append(path)
        inventory.append(report_path)
        reports.append(report)
    if reports[0]["files"] != reports[1]["files"] or reports[0]["geometry"] != reports[1]["geometry"]:
        raise ValueError("published replay does not match frozen inputs and geometry")
    spec = importlib.util.spec_from_file_location("bound_geometry_checker", folder / "verify_same_root_cover.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    if sha(checker.root.__file__) != reports[0]["files"]["verify_contact_root.py"]:
        raise ValueError("root checker code differs from published checker")
    system = json.loads((folder / "SYSTEM.json").read_text())
    certificate = json.loads((folder / "ROOT-CERTIFICATE.json").read_text())
    if certificate["system_sha256"] != sha(folder / "SYSTEM.json"):
        raise ValueError("root system not bound")
    root_result = checker.root.verify(system, certificate, checker.F(1, 10**80))
    geometry_result = checker.geometry_check(system, certificate)
    if root_result != reports[0]["root"] or geometry_result != reports[0]["geometry"]:
        raise ValueError("current exact replay differs from accepted report")
    if not geometry_result["same_root_entire_disk_cover_proved"]:
        raise ValueError("full disk cover missing")
    from fractions import Fraction as F
    if not F(root_result["r_strict_interval"][1]) < F(234701, 10**6):
        raise ValueError("algebraic root not below scope threshold")
    # These families remain necessary for a counterexample to the sharper
    # bound because a radius below R* is also below the older rational U.
    expected_families = [
        {"B": 14, "I": 12, "frontier_nodes": 2},
        {"B": 15, "I": 11, "frontier_nodes": 26},
        {"B": 16, "I": 10, "frontier_nodes": 70},
        {"B": 17, "I": 9, "frontier_nodes": 180},
    ]
    if old_audit["new_family_frontiers_independently_reconstructed"] != expected_families:
        raise ValueError("wrong inherited necessary scope")
    from audit_new_scope_checkpoints import verify_current
    checkpoint_rows, checkpoint_files = verify_current()
    checkpoint_audit_path = out / "n26-new-four-family-checkpoints-v1.json"
    checkpoint_audit = json.loads(checkpoint_audit_path.read_text())
    if checkpoint_audit["families"] != checkpoint_rows or not checkpoint_audit["all_four_current_checkpoints_replayed"]:
        raise ValueError("four-family checkpoint audit differs from current replay")
    for path, digest in checkpoint_audit["files"].items():
        if sha(path) != digest:
            raise ValueError("changed queue audit input")
    inventory.extend(checkpoint_files)
    inventory.append(checkpoint_audit_path)
    report = {
        "schema": "N26-same-root-current-content-bundle-audit-v1",
        "current_bound_bytes_rechecked": True,
        "root_and_geometry_exactly_replayed": True,
        "published_verifier_replay_bound": True,
        "same_root_entire_disk_cover_proved": True,
        "specified_candidate_exact_covering_radius_proved": True,
        "r_strict_interval": root_result["r_strict_interval"],
        "earlier_rational_cover_and_scope_audit_bound": True,
        "necessary_families_inherited_below_rational_threshold": expected_families,
        "four_family_checkpoints_replayed": checkpoint_rows,
        "external_published_n8_theorem_still_explicit": True,
        "arbitrary_cover_reduction_final_acceptance": False,
        "full_catalog_complete": False,
        "local_optimality_proved": False,
        "global_optimality_proved": False,
        "n27_started": False,
        "files": {str(path): sha(path) for path in inventory},
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
