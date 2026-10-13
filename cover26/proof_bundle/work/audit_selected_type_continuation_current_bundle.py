"""Extend the still-current selected-type audit with preserved-node refinement."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
from verify_selected_type_trees import read
from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--old-audit", type=Path, required=True)
    parser.add_argument("--original-parent-audit", type=Path, required=True)
    parser.add_argument("--types", type=Path, required=True)
    parser.add_argument("--types-replay", type=Path, required=True)
    parser.add_argument("--frontier", type=Path, required=True)
    parser.add_argument("--frontier-replay", type=Path, required=True)
    parser.add_argument("--continuation", type=Path, required=True)
    parser.add_argument("--narrative", type=Path, required=True)
    parser.add_argument("--base-output", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.base_output.exists():
        raise FileExistsError("fresh selected-type continuation audit paths required")
    old = read(args.old_audit)
    if not old["current_bound_bytes_rechecked"] or old["global_optimality_proved"]:
        raise ValueError("previous selected-type current audit is not accepted")
    inventory = dict(old["files"])
    inventory[linux(args.old_audit)] = sha(args.old_audit)
    for text, digest in inventory.items():
        if sha(local_path(text)) != digest:
            raise ValueError("previous selected-type full-chain binding changed")
    continuation = read(args.continuation)
    if (not continuation["verified"]
            or not continuation["all_prior_non_OPEN_nodes_and_closed_splits_unchanged"]
            or continuation["new_acceptance_sha256"] != sha(args.types / "VERIFIED.json")):
        raise ValueError("continued trees have no current paid-node preservation proof")
    for text, digest in continuation["files"].items():
        if sha(local_path(text)) != digest:
            raise ValueError("continued-type preservation input changed")
    inventory.update(continuation["files"])
    base_script = Path(__file__).with_name("audit_selected_types_current_bundle.py")
    if inventory.get(linux(base_script)) != sha(base_script):
        raise ValueError("base audit is not the same script bound by the previous audit")
    command = [sys.executable, str(base_script),
               "--parent-audit", str(args.original_parent_audit),
               "--types", str(args.types), "--types-published-replay", str(args.types_replay),
               "--frontier", str(args.frontier), "--frontier-published-replay", str(args.frontier_replay),
               "--narrative", str(args.narrative), "--output", str(args.base_output)]
    run = subprocess.run(command, check=False)
    if run.returncode:
        raise ValueError("fresh continued-type current full-chain composition failed")
    base = read(args.base_output)
    for text, digest in base["files"].items():
        if text in inventory and inventory[text] != digest:
            raise ValueError("old and continued current audits disagree on shared bound bytes")
        inventory[text] = digest
    for path in (args.base_output, args.continuation, Path(__file__)):
        inventory[linux(path)] = sha(path)
    for text, digest in inventory.items():
        if sha(local_path(text)) != digest:
            raise ValueError("continued-type current bytes changed during final binding")
    report = {**{key: value for key, value in base.items() if key != "files"},
              "schema": "N26-current-full-chain-plus-preserved-selected-type-continuation-audit-v1",
              "previous_selected_type_current_audit_still_bound": True,
              "previous_selected_type_current_audit_sha256": sha(args.old_audit),
              "all_previously_paid_type_nodes_and_closed_splits_preserved": True,
              "previous_non_OPEN_type_nodes_preserved": continuation["previous_non_OPEN_nodes_preserved"],
              "new_closed_type_indices_in_this_continuation": continuation["new_closed_competitor_type_indices"],
              "files": inventory}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
