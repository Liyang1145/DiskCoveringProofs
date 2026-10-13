"""Publish a separate Rstar frontier; never alter any original U queue."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--types", type=Path, required=True)
    parser.add_argument("--types-published-replay", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted = bound(args.types)[0]
    if read(args.types_published_replay) != accepted:
        raise ValueError("type published replay not yet accepted")
    args.output.mkdir(parents=True)
    copies = [(args.types / original, name) for original, name in (
        ("VERIFIED.json", "SOURCE-TYPE-ACCEPTANCE.json"),
        ("CLASSIFICATION.json", "SOURCE-CLASSIFICATION.json"),
        ("CERTIFICATE.json", "SOURCE-TYPE-CERTIFICATE.json"),
        ("PENDING-TYPES.json", "SOURCE-PENDING-TYPES.json"),
        ("CANDIDATE-POSITIVE-CONTROL.json", "CANDIDATE-POSITIVE-CONTROL.json"),
        ("CATALOG-SOURCE/SOURCE-FRONTIER.json", "SOURCE-ORIGINAL-U-FRONTIER.json"),
        ("CATALOG-SOURCE/SOURCE-ACCEPTANCE.json", "SOURCE-ORIGINAL-U-ACCEPTANCE.json"))]
    copies.extend((args.types / name, name) for name in accepted["files"] if "/" not in name and name.endswith(".py"))
    copies.extend((Path(__file__).with_name(name), name) for name in
                  ("verify_selected_Rstar_frontier.py", "build_selected_Rstar_frontier.py"))
    proof = Path(__file__).with_name("n26-selected-Rstar-frontier-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PARTITION-PROOF.md")
    copies.append((proof, "PARTITION-PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {"schema": "N26-selected-Rstar-competitor-frontier-input-bindings-v1",
                "source_types": linux(args.types),
                "source_types_published_replay": linux(args.types_published_replay),
                "source_acceptance_sha256": sha(args.types / "VERIFIED.json"),
                "copied_files": {name: sha(args.output / name) for _, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    run = subprocess.run([sys.executable, str(args.output / "verify_selected_Rstar_frontier.py"),
                          "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=False)
    if run.returncode:
        raise ValueError("conditional frontier exact acceptance failed; incomplete bundle preserved")


if __name__ == "__main__":
    main()
