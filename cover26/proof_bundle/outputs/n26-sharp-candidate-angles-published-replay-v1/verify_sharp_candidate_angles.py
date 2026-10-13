"""Publish an exactly replayed candidate-angle partition, preserving OPEN boxes."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from n26_force import load_trig
from n26_direct_arc_force import regular_ring_controls
import n26_sharp_candidate_angles as sharp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = json.loads(args.proposal.read_text())
    spec, radius_upper, cells, sources, inventory = sharp.input_gate(
        args.stress, args.local, args.transport, args.pinning, proposal)
    arcs = load_trig()[0]
    nodes = proposal["nodes"]
    result, pending, ledger = sharp.replay(spec, radius_upper, cells, nodes, arcs)
    controls = regular_ring_controls(arcs)
    negatives = []

    def reject(label, changed):
        try:
            sharp.replay(spec, radius_upper, cells, changed, arcs)
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad sharp candidate partition accepted: " + label)

    bad = deepcopy(nodes)
    row = next(n for n in bad if n["kind"] == "SPLIT")
    row["children"][1] = row["children"][0]
    reject("lost-closed-angular-half", bad)
    bad = deepcopy(nodes)
    bad.append({"kind": "OPEN"})
    reject("unreachable-unresolved-box", bad)
    reject("broad-root-box-falsely-treated-as-local", [{"kind": "LOCAL"}])
    bad = deepcopy(nodes)
    open_row = next((n for n in bad if n["kind"] == "OPEN"), bad[0])
    open_row["kind"] = "CLOSED"
    reject("unproved-open-box-called-closed", bad)
    bad = deepcopy(nodes)
    force = next((n for n in bad if n["kind"] == "FORCE"), None)
    if force is not None:
        for key in ("g", "f"):
            force["cert"][key] = [0] * len(force["cert"][key])
        reject("zero-sharp-force", bad)
    args.output.mkdir(parents=True)
    certificate = {"schema": "N26-sharp-candidate-partial-angle-partition-v1",
                   "radius_scope": "same-root-Rstar", "spec": spec,
                   "source_acceptance_sha256": sources, "nodes": nodes}
    (args.output / "CERTIFICATE.json").write_text(json.dumps(certificate, separators=(",", ":")) + "\n", encoding="utf-8")
    (args.output / "PENDING-ANGLES.json").write_text(json.dumps(pending, separators=(",", ":")) + "\n", encoding="utf-8")
    (args.output / "LOWER-LEDGER.json").write_text(json.dumps(ledger, separators=(",", ":")) + "\n", encoding="utf-8")
    files = ["CERTIFICATE.json", "PENDING-ANGLES.json", "LOWER-LEDGER.json"]
    modules = [
        "verify_sharp_candidate_angles.py", "n26_sharp_candidate_angles.py", "n26_force.py", "n26_direct_arc_force.py",
        "verify_degree_area.py", "verify_anchor_pinning.py", "verify_contact_root.py",
        "verify_same_root_cover.py", "audit_prefix_origin.py", "audit_prefix_partition.py",
    ]
    for name in modules:
        source = Path(__file__).with_name(name)
        (args.output / name).write_bytes(source.read_bytes())
        files.append(name)
    (args.output / "exact_arcs.py").write_bytes(Path(arcs.__file__).read_bytes())
    files.append("exact_arcs.py")
    proof = Path(__file__).with_name("n26-sharp-candidate-angles-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files.append("PROOF.md")
    report = {
        "schema": "N26-sharp-candidate-partial-angle-partition-acceptance-v1",
        "verified": True, **result,
        "candidate_complete_transport_prefix": json.loads((args.transport / "CANDIDATE-PATH.json").read_text())["prefix"],
        "radius_comparison_uses_certified_Rstar_upper_not_U": True,
        "Rstar_strict_upper_endpoint": str(radius_upper),
        "source_acceptance_sha256": sources,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "full_catalog_complete": False, "global_lower_bound_proved": False, "global_optimality_proved": False,
        "formal_machine_geometry_proof": False, "negative_controls_rejected": negatives,
        "direct_arc_force_positive_controls": controls,
        "files": {name: sharp.pin.sha(args.output / name) for name in files},
        "source_files": {str(path): sharp.pin.sha(path) for path in inventory},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files", "candidate_complete_transport_prefix")},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()
