"""Exact source-bound continuation of the accepted refined angular tree."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import verify_refined_candidate_angles as prior_checker
from n26_force import load_trig


def lineage_gate(source_nodes, nodes):
    if len(nodes) < len(source_nodes):
        raise ValueError("continued angular tree lost existing nodes")
    changed = []
    for i, old in enumerate(source_nodes):
        new = nodes[i]
        if old["kind"] != "OPEN":
            if old != new:
                raise ValueError("continued tree erased or changed a previously proved node")
        elif new != old:
            if new.get("kind") not in ("SPLIT", "FORCE", "LOCAL", "EMPTY"):
                raise ValueError("unproved replacement of retained OPEN box")
            if new["kind"] == "SPLIT" and any(k < len(source_nodes) for k in new["children"]):
                raise ValueError("new subtree reuses pre-existing nodes instead of its own descendants")
            changed.append(i)
    return changed


def input_gate(source_folder, original_folder, pinning_basis, stress_folder, local_folder,
               transport_folder, source_pinning, new_pinning, proposal):
    old_report, inventory = prior_checker.bound(source_folder)
    if prior_checker.sharp.pin.sha(prior_checker.__file__) != old_report["files"]["verify_refined_candidate_angles.py"]:
        raise ValueError("changed accepted source partition reconstruction")
    source, old_result, old_pending, old_ledger, paths, old_pin_result, _, _ = prior_checker.reconstruct(
        original_folder, pinning_basis, stress_folder, local_folder, transport_folder, source_pinning)
    inventory.extend(paths)
    if (source != json.loads((source_folder / "CERTIFICATE.json").read_text())
            or any(old_report[key] != value for key, value in old_result.items())
            or old_pending != json.loads((source_folder / "PENDING-ANGLES.json").read_text())
            or old_ledger != json.loads((source_folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("starting accepted refined tree is not reconstructed")
    if (proposal["refinement_source_acceptance_sha256"] != prior_checker.sharp.pin.sha(source_folder / "VERIFIED.json")
            or proposal["refinement_source_certificate_sha256"] != prior_checker.sharp.pin.sha(source_folder / "CERTIFICATE.json")
            or proposal["source_acceptance_sha256"] != source["source_acceptance_sha256"]
            or proposal["radius_scope"] != "same-root-Rstar" or proposal["spec"] != source["spec"]):
        raise ValueError("discovery continuation is not bound to this accepted angular partition")
    pin_report, paths = prior_checker.bound(new_pinning)
    inventory.extend(paths)
    refined = prior_checker.refined
    if prior_checker.sharp.pin.sha(refined.__file__) != pin_report["files"]["verify_refined_anchor_pinning.py"]:
        raise ValueError("new pinning checker differs from accepted exact arithmetic")
    pin_proposal = json.loads((new_pinning / "CERTIFICATE.json").read_text())
    data = refined.source_gate(pinning_basis, stress_folder, local_folder, transport_folder, pin_proposal)
    inventory.extend(data[5])
    pin_result = refined.derive(*data[:5], pin_proposal)
    if any(pin_report[key] != value for key, value in pin_result.items()):
        raise ValueError("larger pinning angle domain does not replay")
    cells = [tuple(map(F, row)) for row in pin_result["closed_anchor_angle_cells"]]
    if any(not a <= F(lo) <= F(hi) <= b
           for (a, b), (lo, hi) in zip(cells, old_pin_result["closed_anchor_angle_cells"])):
        raise ValueError("larger pinning box does not contain the previously accepted LOCAL domain")
    radius_upper = F(json.loads((stress_folder / "VERIFIED.json").read_text())["modified_root_check"]["r_strict_interval"][1])
    return source, old_report, pin_result, cells, radius_upper, inventory


def replay_continuation(source, old_report, pin_result, cells, radius_upper, proposal, arcs):
    discovered = deepcopy(proposal["nodes"])
    changed = lineage_gate(source["nodes"], discovered)
    discovery_result, discovery_pending, discovery_ledger = prior_checker.sharp.replay(
        source["spec"], radius_upper, cells, discovered, arcs)
    nodes = deepcopy(discovered)
    newly_local = []
    for row in discovery_pending:
        if all(a <= F(lo) <= F(hi) <= b
               for lo, hi, (a, b) in zip(row["lower"], row["upper"], cells)):
            nodes[row["index"]] = {"kind": "LOCAL"}
            newly_local.append(row["index"])
    newly_local.sort()
    lineage_gate(discovered, nodes)
    lineage_gate(source["nodes"], nodes)
    result, pending, ledger = prior_checker.sharp.replay(source["spec"], radius_upper, cells, nodes, arcs)
    delta_counts = {kind: result["counts"][kind] - old_report["counts"][kind] for kind in result["counts"]}
    return nodes, result, pending, ledger, changed, newly_local, delta_counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--original", type=Path, required=True)
    parser.add_argument("--pinning-basis", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--source-pinning", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = json.loads(args.proposal.read_text())
    source, old_report, pin_result, cells, radius_upper, inventory = input_gate(
        args.source, args.original, args.pinning_basis, args.stress, args.local,
        args.transport, args.source_pinning, args.pinning, proposal)
    arcs = load_trig(args.source)[0]
    nodes, result, pending, ledger, changed, newly_local, delta_counts = replay_continuation(
        source, old_report, pin_result, cells, radius_upper, proposal, arcs)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("bad continued angular certificate accepted: " + label)

    bad = deepcopy(nodes)
    i = next(i for i, n in enumerate(source["nodes"]) if n["kind"] == "FORCE")
    bad[i] = {"kind": "OPEN"}
    reject("source-force-leaf-erased", lambda: lineage_gate(source["nodes"], bad))
    bad = deepcopy(nodes)
    row = next(n for n in bad[len(source["nodes"]):] if n["kind"] == "SPLIT")
    row["children"][1] = row["children"][0]
    reject("new-split-lost-closed-half", lambda: prior_checker.sharp.replay(
        source["spec"], radius_upper, cells, bad, arcs))
    bad = deepcopy(nodes)
    bad.append({"kind": "OPEN"})
    reject("unreachable-pending-leaf", lambda: prior_checker.sharp.replay(
        source["spec"], radius_upper, cells, bad, arcs))
    bad = deepcopy(proposal)
    bad["refinement_source_acceptance_sha256"] = "0" * 64
    reject("changed-source-acceptance", lambda: input_gate(
        args.source, args.original, args.pinning_basis, args.stress, args.local,
        args.transport, args.source_pinning, args.pinning, bad))
    reject("broad-root-falsely-paid-as-local", lambda: prior_checker.sharp.replay(
        source["spec"], radius_upper, cells, [{"kind": "LOCAL"}], arcs))
    controls = prior_checker.direct.regular_ring_controls(arcs)
    sources = {
        **source["source_acceptance_sha256"],
        "starting_partition": prior_checker.sharp.pin.sha(args.source / "VERIFIED.json"),
        "refined_pinning": prior_checker.sharp.pin.sha(args.pinning / "VERIFIED.json"),
    }
    certificate = {
        "schema": "N26-source-bound-continued-sharp-candidate-angle-tree-v1",
        "radius_scope": "same-root-Rstar", "spec": source["spec"],
        "source_acceptance_sha256": sources,
        "source_certificate_sha256": prior_checker.sharp.pin.sha(args.source / "CERTIFICATE.json"),
        "nodes": nodes,
    }
    args.output.mkdir(parents=True)
    for name, value in (("CERTIFICATE.json", certificate), ("PENDING-ANGLES.json", pending), ("LOWER-LEDGER.json", ledger)):
        (args.output / name).write_text(json.dumps(value, separators=(",", ":")) + "\n", encoding="utf-8")
    (args.output / "SOURCE-CERTIFICATE.json").write_bytes((args.source / "CERTIFICATE.json").read_bytes())
    (args.output / "SOURCE-ACCEPTANCE.json").write_bytes((args.source / "VERIFIED.json").read_bytes())
    (args.output / "PROPOSAL.json").write_bytes(args.proposal.read_bytes())
    files = ["CERTIFICATE.json", "PENDING-ANGLES.json", "LOWER-LEDGER.json",
             "SOURCE-CERTIFICATE.json", "SOURCE-ACCEPTANCE.json", "PROPOSAL.json"]
    for name in old_report["files"]:
        if name.endswith(".py"):
            (args.output / name).write_bytes((args.source / name).read_bytes())
            files.append(name)
    (args.output / "verify_continued_candidate_angles.py").write_bytes(Path(__file__).read_bytes())
    files.append("verify_continued_candidate_angles.py")
    (args.output / "BASE-ANGLE-PROOF.md").write_bytes((args.original / "PROOF.md").read_bytes())
    files.append("BASE-ANGLE-PROOF.md")
    proof = Path(__file__).with_name("n26-continued-candidate-angles-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files.append("PROOF.md")
    report = {
        "schema": "N26-continued-refined-candidate-angle-partition-acceptance-v1",
        "verified": True, **result,
        "source_acceptance_sha256": sources,
        "source_unresolved_angle_boxes": old_report["unresolved_closed_angle_boxes"],
        "source_proved_nodes_and_closed_splits_preserved": True,
        "source_OPEN_roots_refined": changed,
        "newly_local_descendant_indices_from_wider_pinning": newly_local,
        "event_count_differences": delta_counts,
        "new_strict_force_boxes": delta_counts["FORCE"],
        "new_paid_LOCAL_boxes": delta_counts["LOCAL"],
        "direct_arc_force_positive_controls": controls,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "formal_machine_geometry_proof": False,
        "negative_controls_rejected": negatives,
        "files": {name: prior_checker.sharp.pin.sha(args.output / name) for name in dict.fromkeys(files)},
        "source_files": {str(path): prior_checker.sharp.pin.sha(path) for path in inventory},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    excluded = {"files", "source_files", "source_OPEN_roots_refined", "newly_local_descendant_indices_from_wider_pinning"}
    print(json.dumps({key: value for key, value in report.items() if key not in excluded}, indent=2), flush=True)


if __name__ == "__main__":
    main()
