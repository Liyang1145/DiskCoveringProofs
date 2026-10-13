"""Independent replay of a preserved sharp tree with correlated-force leaves."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_correlated_arc_force as correlated
from n26_force import load_trig
import verify_sharp_constraint_candidate_angles as previous


CORRELATED = "SHARP_CORRELATED_FORCE"
KINDS = (*previous.tree.KINDS, CORRELATED)
sha = previous.caps_checker.checker.sharp.pin.sha


def lineage_gate(old, nodes):
    if not isinstance(nodes, list) or len(nodes) < len(old):
        raise ValueError("correlated continuation lost source nodes")
    for i, original in enumerate(old):
        new = nodes[i]
        if original["kind"] != "OPEN" and new != original:
            raise ValueError("correlated continuation changed a previously paid node")
        if original["kind"] == "OPEN" and original != new:
            if new.get("kind") not in KINDS or new["kind"] == "OPEN":
                raise ValueError("invalid correlated replacement")
            if new["kind"] == "SPLIT" and any(k < len(old) for k in new["children"]):
                raise ValueError("correlated split reuses old nodes")


def source_gate(source_folder, historical, pinning_basis, stress, local, transport, pinning, caps):
    accepted, inventory = previous.caps_checker.checker.bound(source_folder)
    for name, digest in accepted["files"].items():
        path = Path(__file__).with_name(name)
        if name.endswith(".py") and path.exists() and sha(path) != digest:
            raise ValueError("correlated source gate imported changed accepted arithmetic: " + name)
    proposal = json.loads((source_folder / "PROPOSAL.json").read_text())
    old, old_report, radius, cells, matrix, cap_certificate, inputs = previous.input_gate(
        historical, pinning_basis, stress, local, transport, pinning, caps, proposal)
    inventory.extend(inputs)
    nodes, result, pending, ledger, empty, paid_local, strict_new, local_new = previous.replay_and_close(
        old, old_report, radius, cells, matrix, proposal, load_trig(source_folder)[0])
    sources = {
        "starting_partition": sha(historical / "VERIFIED.json"),
        "sharp_constraint_interface": sha(caps / "VERIFIED.json"),
        "pinning": sha(pinning / "VERIFIED.json"), "stress": sha(stress / "VERIFIED.json"),
        "local": sha(local / "VERIFIED.json"), "transport": sha(transport / "VERIFIED.json")}
    certificate = {
        "schema": "N26-sharp-radius-conditional-closed-angular-tree-v1",
        "radius_scope": "same-root-Rstar", "spec": old["spec"],
        "source_acceptance_sha256": sources, "nodes": nodes}
    if (any(accepted[key] != value for key, value in result.items())
            or certificate != json.loads((source_folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((source_folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((source_folder / "LOWER-LEDGER.json").read_text())
            or strict_new != accepted["new_strict_force_angle_boxes"]
            or local_new != accepted["new_paid_LOCAL_angle_boxes"]
            or empty != accepted["automatically_paid_sharp_empty_indices"]
            or paid_local != accepted["automatically_paid_sharp_local_indices"]):
        raise ValueError("accepted conditional source tree did not independently replay")
    return certificate, accepted, radius, cells, matrix, cap_certificate, pending, inventory


def replay(spec, radius, cells, matrix, nodes, arcs):
    ordinary = deepcopy(nodes)
    for node in ordinary:
        if node.get("kind") == CORRELATED:
            if set(node) != {"kind", "cert"}:
                raise ValueError("malformed correlated leaf")
            node.clear()
            node["kind"] = "OPEN"
    result, pending, ledger = previous.tree.replay(spec, radius, cells, matrix, ordinary, arcs)
    remaining, paid, margins = [], 0, []
    for row in pending:
        node = nodes[row["index"]]
        if node["kind"] != CORRELATED:
            remaining.append(row)
            continue
        if row["sharp_radius_domain_empty"]:
            raise ValueError("correlated force must have a nonempty sharp box")
        value = correlated.force_check(
            spec, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])),
            matrix, node["cert"], arcs)
        margin = F(value["required_radius_lower"]) - radius
        if margin <= 0:
            raise ValueError("correlated force is not strictly above the certified root endpoint")
        ledger.append({**row, "kind": CORRELATED, **value,
                       "strict_margin_above_Rstar_upper": str(margin),
                       "uses_radius_conditional_sharp_constraints": True})
        paid += 1
        margins.append(margin)
    result["counts"]["OPEN"] -= paid
    result["counts"][CORRELATED] = paid
    result["unresolved_closed_angle_boxes"] = len(remaining)
    result["all_radius_at_most_Rstar_candidate_domains_lower_bounded"] = not remaining
    result["candidate_transport_global_lower_bound_proved"] = not remaining
    if result["minimum_strict_force_margin_above_Rstar_upper"] is not None:
        margins.append(F(result["minimum_strict_force_margin_above_Rstar_upper"]))
    result["minimum_strict_force_margin_above_Rstar_upper"] = str(min(margins)) if margins else None
    ledger.sort(key=lambda row: row["index"])
    return result, remaining, ledger


def replay_and_close(source, radius, cells, matrix, proposal, arcs):
    nodes = deepcopy(proposal["nodes"])
    lineage_gate(source["nodes"], nodes)
    _, pending, _ = replay(source["spec"], radius, cells, matrix, nodes, arcs)
    empty, local = [], []
    for row in pending:
        if row["sharp_radius_domain_empty"]:
            nodes[row["index"]] = {"kind": "SHARP_EMPTY"}
            empty.append(row["index"])
        elif row["sharp_radius_domain_inside_local"]:
            nodes[row["index"]] = {"kind": "SHARP_LOCAL"}
            local.append(row["index"])
    lineage_gate(source["nodes"], nodes)
    result, pending, ledger = replay(source["spec"], radius, cells, matrix, nodes, arcs)
    return nodes, result, pending, ledger, empty, local


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "historical", "pinning-basis", "stress", "local", "transport",
                 "pinning", "caps", "proposal", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    source, old_report, radius, cells, matrix, cap_certificate, old_pending, inventory = source_gate(
        args.source, args.historical, args.pinning_basis, args.stress, args.local,
        args.transport, args.pinning, args.caps)
    proposal = json.loads(args.proposal.read_text())
    if (proposal["source_acceptance_sha256"] != sha(args.source / "VERIFIED.json")
            or proposal["source_certificate_sha256"] != sha(args.source / "CERTIFICATE.json")
            or proposal["spec"] != source["spec"] or proposal["radius_scope"] != "same-root-Rstar"):
        raise ValueError("correlated proposal changed accepted graph or radius")
    arcs = load_trig(args.source)[0]
    nodes, result, pending, ledger, auto_empty, auto_local = replay_and_close(
        source, radius, cells, matrix, proposal, arcs)
    tiny = [tuple(map(F, row)) for row in cap_certificate["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(lo) <= a <= b <= F(hi) for lo, hi, (a, b) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger if row["kind"] in ("LOCAL", "SHARP_LOCAL"))
    if not retained:
        raise ValueError("correlated continuation lost exact candidate LOCAL control")
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid correlated tree accepted: " + label)

    bad = deepcopy(nodes)
    next(node for node in bad if node["kind"] == "FORCE").clear()
    next_node = next(i for i, node in enumerate(bad) if not node)
    bad[next_node] = {"kind": "OPEN"}
    reject("old-paid-force-erased", lambda: lineage_gate(source["nodes"], bad))
    bad = deepcopy(nodes)
    next(node for node in bad if node["kind"] == "SPLIT")["children"][1] = \
        next(node for node in bad if node["kind"] == "SPLIT")["children"][0]
    reject("closed-split-missing-half", lambda: replay(source["spec"], radius, cells, matrix, bad, arcs))
    reject("unreachable-correlated-open", lambda: replay(
        source["spec"], radius, cells, matrix, nodes + [{"kind": "OPEN"}], arcs))
    first = next((row for row in ledger if row["kind"] == CORRELATED), None)
    if first is not None:
        index = first["index"]
        lo, hi = list(map(F, first["sharp_lower"])), list(map(F, first["sharp_upper"]))
        base = nodes[index]["cert"]
        bad_cert = deepcopy(base)
        bad_cert["mu"] = [[0, 1, "-1"]]
        reject("negative-difference-dual", lambda: correlated.force_check(
            source["spec"], lo, hi, matrix, bad_cert, arcs))
        bad_cert = deepcopy(base)
        bad_cert["mu"] = [[0, 1, "1"], [0, 1, "1"]]
        reject("repeated-difference-dual-edge", lambda: correlated.force_check(
            source["spec"], lo, hi, matrix, bad_cert, arcs))
        bad_cert = deepcopy(base)
        bad_cert["g"] = [0] * len(base["g"])
        bad_cert["f"] = [0] * len(base["f"])
        reject("zero-flow-dual-cannot-prove-radius", lambda: correlated.force_check(
            source["spec"], lo, hi, matrix, bad_cert, arcs))
    controls = correlated.controls(arcs)
    new_direct = result["counts"]["SHARP_FORCE"] - old_report["counts"]["SHARP_FORCE"]
    new_correlated = result["counts"][CORRELATED]
    rescued = sum(F(row["direct_arc_required_radius_lower"]) <= radius
                  for row in ledger if row["kind"] == CORRELATED)
    sources = {"starting_partition": sha(args.source / "VERIFIED.json"),
               "historical_cap_basis": sha(args.historical / "VERIFIED.json"),
               "sharp_caps": sha(args.caps / "VERIFIED.json"),
               "pinning": sha(args.pinning / "VERIFIED.json"),
               "stress": sha(args.stress / "VERIFIED.json"),
               "local": sha(args.local / "VERIFIED.json"),
               "transport": sha(args.transport / "VERIFIED.json")}
    certificate = {"schema": "N26-correlated-sharp-radius-closed-angular-tree-v1",
                   "spec": source["spec"], "radius_scope": "same-root-Rstar",
                   "source_acceptance_sha256": sources, "nodes": nodes}
    args.output.mkdir(parents=True)
    files = []
    for name, data in (("CERTIFICATE.json", certificate), ("PENDING-ANGLES.json", pending),
                       ("LOWER-LEDGER.json", ledger)):
        (args.output / name).write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")
        files.append(name)
    for name in ("CERTIFICATE.json", "VERIFIED.json"):
        destination = "SOURCE-" + ("CERTIFICATE.json" if name == "CERTIFICATE.json" else "ACCEPTANCE.json")
        (args.output / destination).write_bytes((args.source / name).read_bytes())
        files.append(destination)
    (args.output / "PROPOSAL.json").write_bytes(args.proposal.read_bytes())
    files.append("PROPOSAL.json")
    for name in old_report["files"]:
        if name.endswith(".py"):
            (args.output / name).write_bytes((args.source / name).read_bytes())
            files.append(name)
    for name in ("n26_correlated_arc_force.py", "verify_correlated_candidate_angles.py"):
        (args.output / name).write_bytes(Path(__file__).with_name(name).read_bytes())
        files.append(name)
    proof = Path(__file__).with_name("n26-correlated-arc-force-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files.append("PROOF.md")
    report = {
        "schema": "N26-accepted-correlated-candidate-angle-continuation-v1",
        "verified": True, **result, "source_acceptance_sha256": sources,
        "prior_all_proved_nodes_and_closed_splits_preserved": True,
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": retained,
        "new_strict_direct_force_leaves": new_direct,
        "new_strict_correlated_force_leaves": new_correlated,
        "correlated_leaves_not_payable_by_their_direct_arc_bound": rescued,
        "automatically_paid_sharp_empty_indices": auto_empty,
        "automatically_paid_sharp_local_indices": auto_local,
        "exact_correlated_force_positive_controls": controls,
        "discovery_numeric_status_not_used_as_proof": True,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "formal_machine_geometry_proof": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {name: sha(args.output / name) for name in dict.fromkeys(files)},
        "source_files": {str(path): sha(path) for path in inventory}}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
