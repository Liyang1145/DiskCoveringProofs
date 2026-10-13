"""Seal a conditional partition of a later accepted original-U frontier."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
from verify_selected_type_trees import SCOPE, bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--stage-replay", type=Path, required=True)
    parser.add_argument("--types", type=Path, required=True)
    parser.add_argument("--types-replay", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    inputs = {"stage": args.stage, "types": args.types}
    replays = {"stage": args.stage_replay, "types": args.types_replay}
    reports = {key: bound(folder)[0] for key, folder in inputs.items()}
    if any(read(replays[key]) != reports[key] for key in inputs):
        raise ValueError("successive conditional partition requires actual matching published replays")
    partition_source = args.types.parent / "n26-selected-Rstar-competitor-frontier-v2"
    accepted_partition = bound(partition_source)[0]
    if (accepted_partition["radius_scope"] != SCOPE
            or accepted_partition["files"]["verify_selected_type_trees.py"] != reports["types"]["files"]["verify_selected_type_trees.py"]):
        raise ValueError("wrong accepted base partition arithmetic")
    args.output.mkdir(parents=True)
    copies = [
        (args.stage / "VERIFIED.json", "SOURCE-STAGE-ACCEPTANCE.json"),
        (args.stage / "FRONTIER.json", "SOURCE-ORIGINAL-U-FRONTIER.json"),
        (args.types / "VERIFIED.json", "SOURCE-TYPES-ACCEPTANCE.json"),
        (args.types / "CLASSIFICATION.json", "SOURCE-CLASSIFICATION.json"),
        (args.types / "CERTIFICATE.json", "SOURCE-TYPE-CERTIFICATE.json"),
        (args.types / "PENDING-TYPES.json", "SOURCE-PENDING-TYPES.json"),
        (args.types / "CANDIDATE-POSITIVE-CONTROL.json", "CANDIDATE-POSITIVE-CONTROL.json"),
        (partition_source / "verify_selected_Rstar_frontier.py", "verify_selected_Rstar_frontier.py"),
        (partition_source / "VERIFIED.json", "BASE-PARTITION-ACCEPTANCE.json")]
    copies.extend((args.types / name, name) for name in reports["types"]["files"]
                  if "/" not in name and name.endswith(".py"))
    copies.extend((Path(__file__).with_name(name), name) for name in
                  ("verify_successive_Rstar_frontier.py", "build_successive_Rstar_frontier.py"))
    proof = Path(__file__).with_name("n26-successive-Rstar-frontier-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    copies.append((proof, "PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {"schema": "N26-successive-stage-Rstar-frontier-input-bindings-v1", "radius_scope": SCOPE,
                "source_folders": {key: linux(folder) for key, folder in inputs.items()},
                "published_replays": {key: linux(path) for key, path in replays.items()},
                "source_acceptance_sha256": {key: sha(folder / "VERIFIED.json") for key, folder in inputs.items()},
                "copied_files": {name: sha(args.output / name) for _, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    run = subprocess.run([sys.executable, str(args.output / "verify_successive_Rstar_frontier.py"),
                          "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=False)
    if run.returncode:
        raise ValueError("successive Rstar partition exact acceptance failed; incomplete bundle preserved")


if __name__ == "__main__":
    main()
