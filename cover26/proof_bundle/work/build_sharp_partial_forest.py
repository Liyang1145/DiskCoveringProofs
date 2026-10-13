"""Freeze exact partial-subtree sharp forests and execute their standalone gate."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
from verify_selected_type_trees import SCOPE, bound, read
from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--source-replay", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.source)
    if read(args.source_replay) != accepted:
        raise ValueError("partial forest baseline has no actual matching published replay")
    manifest = read(args.source / "MANIFEST.json")
    stage, types = [local_path(manifest["source_folders"][key]) for key in ("stage", "types")]
    proposed = read(args.proposal)
    type_report = read(types / "VERIFIED.json")
    if (proposed["schema"] != "N26-unaccepted-sharp-partial-subtree-forest-v1"
            or proposed["verified"] is not False or proposed["radius_scope"] != SCOPE
            or proposed["source_stage_acceptance_sha256"] != sha(stage / "VERIFIED.json")
            or proposed["source_type_acceptance_sha256"] != sha(types / "VERIFIED.json")
            or proposed["source_cap_acceptance_sha256"] != type_report["source_acceptance_sha256"]["caps"]
            or proposed["radius_upper"] != type_report["radius_upper"]):
        raise ValueError("partial forest proposal changed accepted sources or radius")
    roots = [{key: row[key] for key in ("source_index", "B", "prefix", "spec")}
             | ({"sharp_domain_empty": True} if row.get("sharp_domain_empty") else {"nodes": row["nodes"]})
             for row in proposed["roots"]]
    certificate = {"schema": "N26-sharp-partial-subtree-forest-certificate-v1", "radius_scope": SCOPE,
                   "radius_upper": proposed["radius_upper"],
                   "source_conditional_acceptance_sha256": sha(args.source / "VERIFIED.json"), "roots": roots}
    args.output.mkdir(parents=True)
    copies = [
        (args.source / "VERIFIED.json", "SOURCE-CONDITIONAL-ACCEPTANCE.json"),
        (args.source / "RSTAR-COMPETITOR-FRONTIER.json", "SOURCE-RSTAR-FRONTIER.json"),
        (stage / "FRONTIER.json", "SOURCE-ORIGINAL-U-FRONTIER.json"),
        (args.proposal, "PROPOSAL.json")]
    copies.extend((args.source / name, name) for name in accepted["files"] if name.endswith(".py") and "/" not in name)
    copies.extend((Path(__file__).with_name(name), name) for name in
                  ("n26_sharp_partial_domains.py", "verify_sharp_partial_forest.py", "build_sharp_partial_forest.py"))
    copies.append((types / "exact_arcs.py", "exact_arcs.py"))
    proof = Path(__file__).with_name("n26-sharp-partial-forest-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    copies.append((proof, "PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    (args.output / "CERTIFICATE.json").write_text(json.dumps(certificate, separators=(",", ":")) + "\n", encoding="utf-8")
    final_manifest = {
        "schema": "N26-sharp-partial-subtree-forest-input-bindings-v1", "radius_scope": SCOPE,
        "source_conditional_frontier": linux(args.source),
        "source_conditional_published_replay": linux(args.source_replay),
        "source_conditional_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "copied_files": {name: sha(args.output / name) for _, name in copies}}
    final_manifest["copied_files"]["CERTIFICATE.json"] = sha(args.output / "CERTIFICATE.json")
    (args.output / "MANIFEST.json").write_text(json.dumps(final_manifest, indent=2) + "\n", encoding="utf-8")
    run = subprocess.run([sys.executable, str(args.output / "verify_sharp_partial_forest.py"),
                          "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=False)
    if run.returncode:
        raise ValueError("sharp partial forest exact acceptance failed; incomplete frozen bundle preserved")


if __name__ == "__main__":
    main()
