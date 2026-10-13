"""Standalone exact quadratic-energy payments on replayed full-type OPEN leaves."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import expanded_type_registry as registry
import n26_quadratic_energy_minorant as energy
import verify_selected_type_trees as typed
import verify_terminal_catalog as catalog


sha = catalog.sha
read = typed.read


def proposal_gate(proposal, registry_hash, kernel_hash):
    if (proposal["schema"] != "N26-unaccepted-full-type-quadratic-negative-curvature-payments-v1"
            or proposal["verified"] is not False or proposal["radius_scope"] != typed.SCOPE
            or proposal["registry_acceptance_sha256"] != registry_hash
            or proposal["kernels_sha256"] != kernel_hash):
        raise ValueError("quadratic discovery changed its full type source, root or scope")


def source_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-full-type-quadratic-overlay-bindings-v1":
        raise ValueError("wrong full-type quadratic bindings")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("quadratic sealed input changed")
    source_folder = catalog.local_path(manifest["source_registry"])
    accepted, inventory = typed.bound(source_folder)
    if (read(catalog.local_path(manifest["source_registry_replay"])) != accepted
            or sha(source_folder / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or sha(registry.__file__) != accepted["files"]["expanded_type_registry.py"]
            or sha(energy.__file__) != manifest["copied_files"]["n26_quadratic_energy_minorant.py"]):
        raise ValueError("quadratic source lacks its actual matching sealed replay")
    values = registry.input_gate(source_folder)
    source_manifest, pool_report, paths, cv, table, pool_rows, pool_pending, pool_domains, pool_cert, radius, caps, arcs, source_cert, positive = values
    inventory.extend(paths)
    inventory.append(catalog.local_path(manifest["source_registry_replay"]))
    classification = read(source_folder / "CLASSIFICATION.json")
    pending = read(source_folder / "PENDING-TYPES.json")
    domains = read(source_folder / "DOMAINS.json")
    if (read(folder / "SOURCE-CERTIFICATE.json") != source_cert
            or read(folder / "SOURCE-PENDING-TYPES.json") != pending
            or read(folder / "SOURCE-CLASSIFICATION.json") != classification
            or read(folder / "SOURCE-DOMAINS.json") != domains
            or accepted["radius_scope"] != typed.SCOPE or str(radius) != accepted["radius_upper"]):
        raise ValueError("quadratic overlay substituted the current full-type proof partition")
    proposal = read(folder / "PROPOSAL.json")
    proposal_gate(proposal, manifest["source_acceptance_sha256"], sha(folder / "KERNELS.json"))
    kernels = read(folder / "KERNELS.json")
    by_group = {row["group_index"]: row for row in classification}
    source_types = {row["group_index"]: row for row in source_cert["types"]}
    pool_types = {row["group_index"]: row for row in pool_cert["types"]}
    current_pending = {row["group_index"]: row for row in pending}
    current_domains = {row["group_index"]: row for row in domains}
    groups = sorted({row["group_index"] for row in proposal["proposals"]})
    replayed_sources = []
    for index in groups:
        if index not in by_group or not current_pending[index]["closed_OPEN_boxes"]:
            raise ValueError("quadratic payment targets the candidate or an already closed type")
        current = source_types[index]
        if current["kind"] == "REUSE":
            original = pool_types[current["pool_type_index"]]
            if original["spec"] != current["spec"]:
                raise ValueError("quadratic source reused a different complete canonical type")
        else:
            original = current
        bare = {"group_index": index, "spec": current["spec"], "nodes": original["nodes"]}
        a, b, c, d = typed.derive(table, {"types": [bare]}, radius, caps, arcs)
        if (any(by_group[index][key] != value for key, value in a[0].items())
                or b[0] != current_pending[index] or d[0]["matrix"] != current_domains[index]["matrix"]):
            raise ValueError("quadratic source's entire old tree, closed boundaries or OPEN did not replay")
        replayed_sources.append({"group_index": index, "nodes": a[0]["nodes"],
                                 "OPEN": len(b[0]["closed_OPEN_boxes"]),
                                 "all_old_force_leaves_and_independent_BFS_partition_replayed": True})
    checked_kernels = []
    for row in kernels:
        index = row["group_index"]
        if index not in by_group or row["certificate"]["spec"] != by_group[index]["spec"]:
            raise ValueError("quadratic kernel changed its full canonical graph")
        checked_kernels.append(energy.kernel_gate(by_group[index]["spec"], row["certificate"]))
    return (manifest, accepted, inventory, cv, table, classification, pending, domains,
            radius, arcs, proposal, kernels, checked_kernels, positive, replayed_sources)


def derive(classification, source_pending, domains, proposal, kernels, checked_kernels, radius, arcs):
    by_group = {row["group_index"]: row for row in classification}
    boxes = {row["group_index"]: {box["index"]: box for box in row["closed_OPEN_boxes"]}
             for row in source_pending}
    matrices = {row["group_index"]: row["matrix"] for row in domains}
    seen, payments, unpaid_checked = set(), [], []
    for item in proposal["proposals"]:
        index, source_index, kernel_index = item["group_index"], item["source_OPEN_index"], item["kernel_index"]
        key = index, source_index
        if (type(index) is not int or type(source_index) is not int or key in seen
                or index not in boxes or source_index not in boxes[index]
                or type(kernel_index) is not int or not 0 <= kernel_index < len(kernels)
                or kernels[kernel_index]["group_index"] != index
                or checked_kernels[kernel_index]["spec"] != by_group[index]["spec"]):
            raise ValueError("duplicate, hidden or mismatched current quadratic OPEN ownership")
        seen.add(key)
        box = boxes[index][source_index]
        result = energy.bound(checked_kernels[kernel_index], matrices[index], box["lower"], box["upper"],
                              item["certificate"], radius, arcs)
        if result["radius_at_most_Rstar_whole_box_excluded"]:
            if F(result["minimum_strict_radius_margin"]) <= 0:
                raise ValueError("quadratic energy payment has no strict radius conversion")
            payments.append({"group_index": index, "spec": by_group[index]["spec"],
                             "source_closed_OPEN_box": box, "kernel_index": kernel_index,
                             "certificate": item["certificate"], **result})
        else:
            unpaid_checked.append({"group_index": index, "source_OPEN_index": source_index,
                                   "minimum_strict_energy_margin": result["minimum_strict_energy_margin"]})
    paid_by_group = {}
    for row in payments:
        paid_by_group.setdefault(row["group_index"], {})[row["source_closed_OPEN_box"]["index"]] = row
    new_classification, pending = deepcopy(classification), deepcopy(source_pending)
    for row, unresolved in zip(new_classification, pending):
        index = row["group_index"]
        if unresolved["group_index"] != index or unresolved["spec"] != row["spec"]:
            raise ValueError("quadratic overlay reordered a full type or its pending boxes")
        paid = paid_by_group.get(index, {})
        original_count = len(unresolved["closed_OPEN_boxes"])
        unresolved["closed_OPEN_boxes"] = [box for box in unresolved["closed_OPEN_boxes"] if box["index"] not in paid]
        if len(unresolved["closed_OPEN_boxes"]) + len(paid) != original_count:
            raise ValueError("quadratic overlay lost a paid or unvisited source box")
        if paid:
            row["counts"]["OPEN"] -= len(paid)
            row["counts"]["QUADRATIC_ENERGY"] = len(paid)
            row["unresolved_closed_boxes"] = len(unresolved["closed_OPEN_boxes"])
            row["radius_at_most_Rstar_type_excluded"] = not unresolved["closed_OPEN_boxes"]
            margins = [F(item["minimum_strict_radius_margin"]) for item in paid.values()]
            if row["minimum_strict_margin"] is not None:
                margins.append(F(row["minimum_strict_margin"]))
            row["minimum_strict_margin"] = str(min(margins))
            row["proof_source"] = "unchanged-full-source-tree-plus-exact-quadratic-energy-OPEN-overlay"
    return new_classification, pending, payments, unpaid_checked


def frontier(source, table, classification, pending, candidate, radius):
    result, removals = registry.partition.derive(source, table, classification, pending, candidate)
    result["schema"] = "N26-quadratic-type-overlay-Rstar-conditional-frontier-v1"
    result["source_radius_conditional_pending_subtrees"] = result.pop("source_original_U_pending_subtrees")
    result["all_nonremoved_source_conditional_states_preserved_byte_semantically"] = result.pop(
        "all_nonremoved_original_U_states_preserved_byte_semantically")
    result["radius_upper"] = str(radius)
    for row in removals:
        row["unchanged_source_radius_conditional_state"] = row.pop("unchanged_original_U_state")
    return result, removals


def identity_control(kernel):
    b, n = kernel["B"], kernel["vertices"] - kernel["B"]
    den, scale = kernel["inverse_denominator"], kernel["scale"]
    anchors = [[F((3 * i + 1) % 7 - 3), F((5 * i + 2) % 11 - 5)] for i in range(b)]
    internal = [[F((7 * i + 3) % 13 - 6), F((11 * i + 4) % 17 - 8)] for i in range(n)]
    points = anchors + internal
    direct = sum(F(w, scale) * sum((points[u][d] - points[v][d])**2 for d in range(2))
                 for (u, v), w in zip(kernel["edges"], kernel["weights"]))
    boundary = sum(F(w, scale * den) * sum((anchors[i][d] - anchors[j][d])**2 for d in range(2))
                   for i, j, w in kernel["pairs"])
    deviation = [[internal[i][d] - sum(F(kernel["harmonic"][i][j], den) * anchors[j][d]
                                       for j in range(b)) for d in range(2)] for i in range(n)]
    residual = sum(F(kernel["matrix"][b + i][b + j], scale) *
                   sum(deviation[i][d] * deviation[j][d] for d in range(2))
                   for i in range(n) for j in range(n) if kernel["matrix"][b + i][b + j])
    if direct != boundary + residual or residual < 0:
        raise AssertionError("independent full-type exact energy identity failed")
    return True


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = source_gate(folder)
    manifest, accepted, inventory, cv, table, classification, source_pending, domains, radius, arcs, proposal, kernels, checked_kernels, positive, replayed = values
    hashes = {linux(path): sha(path) for path in inventory}
    new_classification, pending, payments, unpaid_checked = derive(
        classification, source_pending, domains, proposal, kernels, checked_kernels, radius, arcs)
    if not payments:
        raise ValueError("quadratic overlay has no strict new payments")
    current_frontier, removal = frontier(cv[3], table, new_classification, pending, cv[5], radius)
    source_folder = catalog.local_path(manifest["source_registry"])
    old_frontier = read(source_folder / "RSTAR-COMPETITOR-FRONTIER.json")
    old_removal = read(source_folder / "CONDITIONAL-REMOVAL-LEDGER.json")
    key = lambda row: (row["B"], tuple(row["prefix"]))
    old_states, new_states = {key(row): row for row in old_frontier["pending_states"]}, {
        key(row): row for row in current_frontier["pending_states"]}
    old_paid, new_paid = {key(row): row for row in old_removal}, {key(row): row for row in removal}
    if (not set(new_states) <= set(old_states) or not set(old_paid) <= set(new_paid)
            or set(old_states) - set(new_states) != set(new_paid) - set(old_paid)
            or any(new_states[k] != old_states[k] for k in new_states)
            or any(new_paid[k] != old_paid[k] for k in old_paid)):
        raise ValueError("quadratic terminal filter lost an old payment, sibling or retained OPEN type")
    for row in table["rows"]:
        if row["same_canonical_type_as_known_candidate"] and not any(
                state["B"] == row["B"] and state["prefix"] == row["prefix"] for state in current_frontier["pending_states"]):
            raise ValueError("an isomorphic candidate terminal disappeared")
    positive_controls = {"independent_two_coordinate_exact_energy_identities": 0,
                         "radius_one_unit_anchors_zero_free_nodes_not_falsely_excluded": 0}
    for kernel_index in sorted({row["kernel_index"] for row in payments}):
        identity_control(checked_kernels[kernel_index])
        positive_controls["independent_two_coordinate_exact_energy_identities"] += 1
        payment = next(row for row in payments if row["kernel_index"] == kernel_index)
        reference = payment["certificate"]["reference_turns"]
        point_check = energy.bound(checked_kernels[kernel_index],
                                   next(row["matrix"] for row in domains if row["group_index"] == payment["group_index"]),
                                   reference, reference, payment["certificate"], F(1), arcs)
        if point_check["radius_at_most_Rstar_whole_box_excluded"]:
            raise AssertionError("known feasible radius-one rod placement falsely excluded")
        positive_controls["radius_one_unit_anchors_zero_free_nodes_not_falsely_excluded"] += 1
    energy.positive_ldl([[F(2), F(1)], [F(1), F(2)]])
    for a, c in ((F(-2), F(3)), (F(0), F(5)), (F(-5), F(-1))):
        for k in range(9):
            x = a + (c - a) * F(k, 8)
            if x**2 > (a + c) * x - a * c:
                raise AssertionError("exact closed secant remainder control failed")
    positive_controls["exact_closed_secant_controls"] = 27
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid quadratic overlay accepted: " + label)

    example = payments[0]
    k = example["kernel_index"]
    bad_kernel = deepcopy(kernels[k]["certificate"])
    bad_kernel["inverse_numerators"][0][0] = str(int(bad_kernel["inverse_numerators"][0][0]) + 1)
    reject("changed-full-integer-ground-inverse", lambda: energy.kernel_gate(example["spec"], bad_kernel))
    bad_kernel = deepcopy(kernels[k]["certificate"])
    bad_kernel["weight_numerators"].pop()
    reject("omitted-necessary-rod", lambda: energy.kernel_gate(example["spec"], bad_kernel))
    bad_kernel = deepcopy(kernels[k]["certificate"])
    bad_kernel["weight_numerators"][0] = 0
    reject("nonpositive-energy-weight", lambda: energy.kernel_gate(example["spec"], bad_kernel))
    box = example["source_closed_OPEN_box"]
    matrix = next(row["matrix"] for row in domains if row["group_index"] == example["group_index"])
    reject("negative-curvature-allowance", lambda: energy.curvature_gate(
        checked_kernels[k], matrix, box["lower"], box["upper"], "-1", arcs))
    bad_cert = deepcopy(example["certificate"])
    bad_cert["reference_turns"][0] = str(F(box["upper"][0]) + 1)
    reject("reference-outside-entire-closed-domain", lambda: energy.bound(
        checked_kernels[k], matrix, box["lower"], box["upper"], bad_cert, radius, arcs))
    bad_cert = deepcopy(example["certificate"])
    bad_cert["difference_dual"]["terms"] = [[0, 1, "-1"]]
    reject("negative-difference-dual", lambda: energy.bound(
        checked_kernels[k], matrix, box["lower"], box["upper"], bad_cert, radius, arcs))
    bad = deepcopy(proposal)
    bad["proposals"].append(deepcopy(bad["proposals"][0]))
    reject("duplicate-current-OPEN-payment", lambda: derive(
        classification, source_pending, domains, bad, kernels, checked_kernels, radius, arcs))
    bad = deepcopy(proposal)
    bad["proposals"][0]["source_OPEN_index"] = -1
    reject("hidden-or-already-proved-source-leaf", lambda: derive(
        classification, source_pending, domains, bad, kernels, checked_kernels, radius, arcs))
    bad = deepcopy(proposal)
    bad["radius_scope"] = "unconditional-original-U"
    reject("conditional-energy-promoted-to-U", lambda: proposal_gate(
        bad, manifest["source_acceptance_sha256"], sha(folder / "KERNELS.json")))
    reject("indefinite-matrix-claimed-positive-LDL", lambda: energy.positive_ldl([[F(1), F(2)], [F(2), F(1)]]))
    bad_spec = deepcopy(example["spec"])
    bad_spec["next"] = 25
    reject("full-type-energy-applied-to-partial-ancestor",
           lambda: energy.kernel_gate(bad_spec, kernels[k]["certificate"]))
    certificate = {
        "schema": "N26-exact-full-type-quadratic-energy-OPEN-overlay-v1",
        "radius_scope": typed.SCOPE, "radius_upper": str(radius),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_full_type_trees_left_byte_identical": True,
        "paid_source_OPEN_keys": [[row["group_index"], row["source_closed_OPEN_box"]["index"]] for row in payments]}
    for name, data in (("CERTIFICATE.json", certificate), ("CLASSIFICATION.json", new_classification),
                       ("PENDING-TYPES.json", pending), ("LOWER-LEDGER.json", payments),
                       ("UNPAID-CHECKS.json", unpaid_checked), ("RSTAR-COMPETITOR-FRONTIER.json", current_frontier),
                       ("CONDITIONAL-REMOVAL-LEDGER.json", removal), ("CANDIDATE-POSITIVE-CONTROL.json", positive),
                       ("POSITIVE-CONTROLS.json", positive_controls)):
        typed.publish_or_match(folder / name, data)
    newly_closed = sorted(set(row["group_index"] for row in new_classification if row["radius_at_most_Rstar_type_excluded"])
                          - set(row["group_index"] for row in classification if row["radius_at_most_Rstar_type_excluded"]))
    report = {
        "schema": "N26-accepted-full-type-quadratic-negative-curvature-overlay-v1",
        "verified": True, "radius_scope": typed.SCOPE, "radius_upper": str(radius),
        "r_strict_interval": accepted["r_strict_interval"],
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_current_full_types": accepted["current_distinct_selected_canonical_types"],
        "old_chosen_full_type_force_trees_and_all_OPEN_semantically_replayed": replayed,
        "unchanged_other_type_proofs_reused_with_bound_actual_published_replay_not_claimed_rerun": True,
        "new_strict_whole_box_quadratic_energy_payments": len(payments),
        "minimum_strict_radius_margin": str(min(F(row["minimum_strict_radius_margin"]) for row in payments)),
        "new_complete_full_type_exclusions": newly_closed,
        "new_current_terminal_paths_removed": len(new_paid) - len(old_paid),
        "unresolved_current_competitor_types": sum(not row["radius_at_most_Rstar_type_excluded"] for row in new_classification),
        "unresolved_current_competitor_closed_boxes": sum(len(row["closed_OPEN_boxes"]) for row in pending),
        "conditional_frontier_pending_subtrees": len(current_frontier["pending_states"]),
        "conditional_frontier_families": current_frontier["families"],
        "all_source_paid_nodes_closed_boundaries_unvisited_OPEN_and_candidate_paths_preserved": True,
        "all_integer_inverse_LDL_dual_and_radius_square_checks_recomputed": True,
        "original_angular_energy_convexity_not_assumed": True,
        "no_float_symbolic_or_optimization_library_used_by_standalone_checker": True,
        "positive_controls": positive_controls, "negative_controls_rejected": negatives,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: sha(folder / name) for name in [
            "MANIFEST.json", *manifest["copied_files"], "CERTIFICATE.json", "CLASSIFICATION.json",
            "PENDING-TYPES.json", "LOWER-LEDGER.json", "UNPAID-CHECKS.json",
            "RSTAR-COMPETITOR-FRONTIER.json", "CONDITIONAL-REMOVAL-LEDGER.json",
            "CANDIDATE-POSITIVE-CONTROL.json", "POSITIVE-CONTROLS.json"]},
        "source_files": hashes, "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_quadratic_type_overlay.py"]:
        raise ValueError("quadratic overlay ran a different sealed checker")
    for text, digest in hashes.items():
        if sha(catalog.local_path(text)) != digest:
            raise ValueError("quadratic source bytes changed during replay")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("quadratic input changed during replay")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    source, _ = typed.bound(args.registry)
    args.output.mkdir(parents=True)
    copies = [(args.registry / name, name) for name in source["files"] if name.endswith(".py")]
    copies.extend([(args.registry / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                   (args.registry / "CERTIFICATE.json", "SOURCE-CERTIFICATE.json"),
                   (args.registry / "CLASSIFICATION.json", "SOURCE-CLASSIFICATION.json"),
                   (args.registry / "PENDING-TYPES.json", "SOURCE-PENDING-TYPES.json"),
                   (args.registry / "DOMAINS.json", "SOURCE-DOMAINS.json"),
                   (args.proposal, "PROPOSAL.json"), (args.kernels, "KERNELS.json"),
                   (Path(energy.__file__), "n26_quadratic_energy_minorant.py"),
                   (Path(__file__), "verify_quadratic_type_overlay.py"),
                   (Path(__file__).with_name("n26-quadratic-type-overlay-proof.md"), "PROOF.md")])
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {
        "schema": "N26-full-type-quadratic-overlay-bindings-v1",
        "source_registry": linux(args.registry.resolve()), "source_registry_replay": linux(args.registry_replay.resolve()),
        "source_acceptance_sha256": sha(args.registry / "VERIFIED.json"),
        "copied_files": {name: sha(args.output / name) for _, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    subprocess.run([sys.executable, str(args.output / "verify_quadratic_type_overlay.py"),
                    "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=True)


def main():
    parser = argparse.ArgumentParser()
    for key in ("input", "report", "registry", "registry-replay", "proposal", "kernels", "output"):
        parser.add_argument("--" + key, type=Path)
    args = parser.parse_args()
    if args.input and args.report:
        verify(args.input.resolve(), args.report.resolve())
    elif all((args.registry, args.registry_replay, args.proposal, args.kernels, args.output)):
        build(args)
    else:
        parser.error("provide replay or all quadratic-overlay build inputs")


if __name__ == "__main__":
    main()
