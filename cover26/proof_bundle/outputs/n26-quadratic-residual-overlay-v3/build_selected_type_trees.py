"""Freeze a selected-type proposal, then execute its standalone exact checker."""

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
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    inputs = {"catalog": args.catalog, "caps": args.caps, "stress": args.stress}
    reports = {key: bound(folder)[0] for key, folder in inputs.items()}
    sources = {key: sha(folder / "VERIFIED.json") for key, folder in inputs.items()}
    proposal = read(args.proposal)
    if (proposal["schema"] != "N26-unaccepted-selected-canonical-type-sharp-trees-v1"
            or proposal["verified"] is not False or proposal["radius_scope"] != SCOPE
            or proposal["global_optimality_proved"] is not False
            or proposal["catalog_acceptance_sha256"] != sources["catalog"]
            or proposal["cap_acceptance_sha256"] != sources["caps"]):
        raise ValueError("unaccepted proposal changed selected source, scope, or status")
    types = [{"group_index": row["group_index"], "spec": row["spec"],
              **({"sharp_domain_empty": True} if row.get("sharp_domain_empty")
                 else {"nodes": row["nodes"]})} for row in proposal["proposals"]]
    certificate = {"schema": "N26-selected-canonical-type-sharp-certificates-v1",
                   "radius_scope": SCOPE, "radius_upper": read(args.caps / "CERTIFICATE.json")["radius_upper"],
                   "source_acceptance_sha256": sources, "types": types}
    args.output.mkdir(parents=True)
    copies = []
    for key, dirname in (("catalog", "CATALOG-SOURCE"), ("caps", "CAP-SOURCE"), ("stress", "STRESS-SOURCE")):
        report = reports[key]
        for name in ["VERIFIED.json", *report["files"], *report.get("additional_files", {})]:
            copies.append((inputs[key] / name, dirname + "/" + name))
    root_modules = {
        "catalog": ("audit_prefix_partition.py", "audit_prefix_origin.py", "n26_terminal_canonical.py",
                    "verify_terminal_catalog.py"),
        "caps": ("n26_force.py", "verify_degree_area.py", "exact_arcs.py", "n26_direct_arc_force.py",
                 "n26_sharp_radius_constraints.py", "verify_anchor_pinning.py"),
        "stress": ("verify_positive_stress.py", "verify_contact_root.py", "verify_same_root_cover.py")}
    for key, names in root_modules.items():
        copies.extend((inputs[key] / name, name) for name in names)
    for name in ("n26_correlated_arc_force.py", "n26_sharp_type_tree.py",
                 "verify_selected_type_trees.py", "build_selected_type_trees.py"):
        copies.append((Path(__file__).with_name(name), name))
    correlated_source = args.catalog.parent / "n26-correlated-candidate-angles-v1"
    correlated_report = bound(correlated_source)[0]
    if sha(Path(__file__).with_name("n26_correlated_arc_force.py")) != correlated_report["files"]["n26_correlated_arc_force.py"]:
        raise ValueError("new type check would change accepted correlated-force arithmetic")
    copies.append((correlated_source / "VERIFIED.json", "CORRELATED-SOURCE-ACCEPTANCE.json"))
    proof = Path(__file__).with_name("n26-selected-type-trees-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    copies.extend(((proof, "PROOF.md"), (args.proposal, "PROPOSAL.json")))
    for original, name in copies:
        target = args.output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(original.read_bytes())
    target = args.output / "CERTIFICATE.json"
    target.write_text(json.dumps(certificate, separators=(",", ":")) + "\n", encoding="utf-8")
    manifest = {"schema": "N26-selected-sharp-type-input-bindings-v1", "radius_scope": SCOPE,
                "source_folders": {key: linux(folder) for key, folder in inputs.items()},
                "source_acceptance_sha256": sources,
                "copied_files": {name: sha(args.output / name) for _, name in copies}}
    manifest["copied_files"]["CERTIFICATE.json"] = sha(target)
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    run = subprocess.run([sys.executable, str(args.output / "verify_selected_type_trees.py"),
                          "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=False)
    if run.returncode:
        raise ValueError("selected type exact acceptance failed; preserved incomplete bundle")


if __name__ == "__main__":
    main()
