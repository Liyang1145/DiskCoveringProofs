"""Exact Rstar-conditional closed angle forests on actual partial subtrees."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from n26_force import CAPS, D, load_trig
import n26_correlated_arc_force as correlated
import n26_sharp_partial_domains as independent
import n26_sharp_radius_constraints as constraints
import n26_sharp_type_tree as trees
import verify_selected_type_trees as typed
import verify_successive_Rstar_frontier as transfer
from verify_terminal_catalog import local_path, sha


def input_gate(folder):
    manifest = typed.read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-sharp-partial-subtree-forest-input-bindings-v1" or manifest["radius_scope"] != typed.SCOPE:
        raise ValueError("partial forest input has a wrong conditional scope")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("sealed partial-forest input changed: " + name)
    base_folder = local_path(manifest["source_conditional_frontier"])
    base, inventory = typed.bound(base_folder)
    if (sha(base_folder / "VERIFIED.json") != manifest["source_conditional_acceptance_sha256"]
            or typed.read(local_path(manifest["source_conditional_published_replay"])) != base
            or typed.read(folder / "SOURCE-CONDITIONAL-ACCEPTANCE.json") != base
            or sha(transfer.__file__) != base["files"]["verify_successive_Rstar_frontier.py"]):
        raise ValueError("partial forest has no actual matching baseline conditional replay")
    inventory.append(local_path(manifest["source_conditional_published_replay"]))
    values = transfer.input_gate(base_folder)
    base_manifest, reports, paths, original, table, classification, pending, candidate, group = values
    inventory.extend(paths)
    baseline, old_ledger, members = transfer.derive(original, table, classification, pending, candidate)
    if (baseline != typed.read(base_folder / "RSTAR-COMPETITOR-FRONTIER.json")
            or old_ledger != typed.read(base_folder / "CONDITIONAL-REMOVAL-LEDGER.json")
            or members != typed.read(base_folder / "COMPLETE-MEMBER-TRANSFER.json")):
        raise ValueError("partial forest baseline did not reconstruct")
    if (baseline != typed.read(folder / "SOURCE-RSTAR-FRONTIER.json")
            or original != typed.read(folder / "SOURCE-ORIGINAL-U-FRONTIER.json")):
        raise ValueError("partial forest changed its source partition")
    types_folder = local_path(base_manifest["source_folders"]["types"])
    cap_folder = local_path(typed.read(types_folder / "MANIFEST.json")["source_folders"]["caps"])
    cap_report, paths = typed.bound(cap_folder)
    inventory.extend(paths)
    cap = typed.read(cap_folder / "CERTIFICATE.json")
    radius = F(reports["types"]["radius_upper"])
    arcs, path = load_trig(folder)
    inventory.append(path)
    caps, margins = constraints.cap_gate(radius, cap, arcs)
    if (reports["types"]["source_acceptance_sha256"]["caps"] != sha(cap_folder / "VERIFIED.json")
            or cap_report["source_stress_acceptance_sha256"] != reports["types"]["source_acceptance_sha256"]["stress"]
            or list(map(str, margins)) != cap_report["four_strict_outward_sine_margins"]):
        raise ValueError("partial forest caps are not bound to the same exact covering root")
    for module in (correlated, constraints, trees, typed):
        name = Path(module.__file__).name
        if sha(module.__file__) != reports["types"]["files"][name]:
            raise ValueError("partial forest changed already accepted exact force or tree arithmetic")
    if sha(independent.__file__) != manifest["copied_files"]["n26_sharp_partial_domains.py"]:
        raise ValueError("partial forest independent matrix arithmetic is unbound")
    certificate = typed.read(folder / "CERTIFICATE.json")
    if (certificate["schema"] != "N26-sharp-partial-subtree-forest-certificate-v1"
            or certificate["radius_scope"] != typed.SCOPE or F(certificate["radius_upper"]) != radius
            or certificate["source_conditional_acceptance_sha256"] != sha(base_folder / "VERIFIED.json")):
        raise ValueError("partial forest certificate changed radius or source")
    return manifest, reports, inventory, original, baseline, candidate, radius, caps, arcs, certificate


def derive(original, baseline, candidate, radius, caps, arcs, roots):
    if not isinstance(roots, list):
        raise ValueError("partial forest root list is malformed")
    refs = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in (14, 15, 16, 17)}
    baseline_by_key = {(row["B"], tuple(row["prefix"])): row for row in baseline["pending_states"]}
    seen, excluded, results, pending, ledgers, domains = set(), set(), [], [], [], []
    for proposed in roots:
        index = proposed["source_index"]
        if type(index) is not int or not 0 <= index < len(original["pending_states"]) or index in seen:
            raise ValueError("partial root is repeated or has an invalid original source index")
        seen.add(index)
        state = original["pending_states"][index]
        b, prefix = state["B"], tuple(state["prefix"])
        key = (b, prefix)
        expected_spec = {"N": 26, "B": b, "next": state["next"], "faces": state["faces"]}
        if (proposed["B"] != b or proposed["prefix"] != list(prefix)
                or proposed["spec"] != expected_spec or baseline_by_key.get(key) != state):
            raise ValueError("partial root proof is attached to a different or already removed state")
        if b == 16 and candidate["prefix"][:len(prefix)] == list(prefix):
            raise ValueError("known feasible candidate owner must not be processed as a competitor")
        resolved = refs[b].resolve(prefix)
        if {"B": b, **refs[b].entry(prefix, resolved, refs[b].children(resolved))} != state:
            raise ValueError("partial proof source did not reconstruct from its exact full prefix")
        matrix, derivation = constraints.constraint_matrix(expected_spec, caps)
        alternative, independent_derivation = independent.matrix(expected_spec, caps)
        if matrix != alternative:
            raise ValueError("independent partial-domain center and anchor closures disagree")
        if matrix is None:
            if (set(proposed) != {"source_index", "B", "prefix", "spec", "sharp_domain_empty"}
                    or proposed["sharp_domain_empty"] is not True):
                raise ValueError("conditionally empty partial root has an invalid payment")
            result = {"nodes": 0, "counts": {}, "radius_at_most_Rstar_type_excluded": True,
                      "unresolved_closed_boxes": 0, "minimum_strict_margin": None}
            boxes, ledger = [], []
        else:
            if set(proposed) != {"source_index", "B", "prefix", "spec", "nodes"}:
                raise ValueError("nonempty partial tree has unverified certificate fields")
            for node in proposed["nodes"]:
                if node.get("kind") == "DIRECT_FORCE" and set(node["cert"]) != {"q", "g", "f"}:
                    raise ValueError("partial direct force has unverified coefficient fields")
            result, boxes, ledger = trees.replay(expected_spec, matrix, radius, proposed["nodes"], arcs)
            independent_leaves = typed.independent_partition(expected_spec, alternative, proposed["nodes"])
            actual = [{field: row[field] for field in ("index", "kind", "lower", "upper") if field in row}
                      for row in [*boxes, *ledger]]
            if independent_leaves != sorted(actual, key=lambda row: row["index"]):
                raise ValueError("independent partial closed leaf boxes differ")
        closed = result["radius_at_most_Rstar_type_excluded"]
        if closed:
            excluded.add(key)
        results.append({"source_index": index, "B": b, "prefix": list(prefix), "spec": expected_spec,
                        **{name: value for name, value in result.items() if name != "radius_at_most_Rstar_type_excluded"},
                        "whole_partial_transport_subtree_excluded_for_radius_at_most_Rstar": closed})
        pending.append({"source_index": index, "B": b, "prefix": list(prefix),
                        "closed_OPEN_boxes": boxes})
        ledgers.append({"source_index": index, "B": b, "prefix": list(prefix),
                        "strict_radius_conditional_leaves": ledger})
        domains.append({"source_index": index, "matrix": matrix,
                        "all_pairs_Bellman_Ford_derivation": derivation,
                        "independent_BFS_Floyd_derivation": independent_derivation})
    kept = [row for row in baseline["pending_states"] if (row["B"], tuple(row["prefix"])) not in excluded]
    if len(kept) + len(excluded) != len(baseline["pending_states"]):
        raise ValueError("partial forest conditional partition lost a whole source node")
    owners = [row for row in kept if row["B"] == 16 and candidate["prefix"][:len(row["prefix"])] == row["prefix"]]
    if len(owners) != 1 or owners[0]["prefix"] != candidate["prefix"]:
        raise ValueError("partial forest lost the unique complete known candidate")
    families = [{"B": b, "I": 26 - b, "pending_subtrees": sum(row["B"] == b for row in kept),
                 "pending_terminal_subtrees": sum(row["B"] == b and row["terminal"] for row in kept)}
                for b in (14, 15, 16, 17)]
    frontier = {"schema": "N26-Rstar-conditional-partial-force-forest-frontier-v1",
                "radius_scope": typed.SCOPE, "source_conditional_pending_subtrees": len(baseline["pending_states"]),
                "new_sharp_partial_whole_subtrees_excluded": len(excluded),
                "families": families, "pending_states": kept,
                "all_unattempted_and_unclosed_whole_subtrees_preserved": True,
                "known_candidate_unique_complete_terminal": candidate["prefix"],
                "original_U_frontier_rewritten": False, "global_optimality_proved": False}
    return frontier, results, pending, ledgers, domains


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    manifest, reports, inventory, original, baseline, candidate, radius, caps, arcs, certificate = input_gate(args.input)
    digests = {linux(path): sha(path) for path in inventory}
    frontier, results, pending, ledgers, domains = derive(original, baseline, candidate, radius, caps, arcs, certificate["roots"])
    controls = correlated.controls(arcs)
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid sharp partial forest accepted: " + label)

    roots = certificate["roots"]
    reject("duplicate-partial-root", lambda: derive(original, baseline, candidate, radius, caps, arcs, roots + roots[:1]))
    bad = deepcopy(roots[:1])
    bad[0]["spec"]["faces"][0] ^= 1 << 25
    reject("partial-force-on-different-face-complex", lambda: derive(original, baseline, candidate, radius, caps, arcs, bad))
    first = next(row for row in roots if "nodes" in row)
    bad = deepcopy(first)
    bad["nodes"] = [{"kind": "EMPTY"}]
    reject("nonempty-partial-root-declared-empty", lambda: derive(original, baseline, candidate, radius, caps, arcs, [bad]))
    bad = deepcopy(first)
    split = next(node for node in bad["nodes"] if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("partial-angle-closed-half-lost", lambda: derive(original, baseline, candidate, radius, caps, arcs, [bad]))
    bad = deepcopy(first)
    bad["nodes"].append({"kind": "OPEN"})
    reject("unvisited-partial-OPEN", lambda: derive(original, baseline, candidate, radius, caps, arcs, [bad]))
    bad = deepcopy(first)
    node = next(node for node in bad["nodes"] if node["kind"] == "CORRELATED_FORCE")
    node["cert"]["mu"] = [[0, 1, "-1"]]
    reject("negative-partial-difference-dual", lambda: derive(original, baseline, candidate, radius, caps, arcs, [bad]))
    index = next(i for i, row in enumerate(original["pending_states"]) if row["B"] == 16 and row["prefix"] == candidate["prefix"])
    state = original["pending_states"][index]
    bad = {"source_index": index, "B": 16, "prefix": candidate["prefix"],
           "spec": {"N": 26, "B": 16, "next": 26, "faces": state["faces"]}, "nodes": [{"kind": "EMPTY"}]}
    reject("known-candidate-owner-paid-as-partial-competitor",
           lambda: derive(original, baseline, candidate, radius, caps, arcs, [bad]))
    for name, value in (("RSTAR-COMPETITOR-FRONTIER.json", frontier), ("CLASSIFICATION.json", results),
                        ("PENDING-PARTIAL-ANGLES.json", pending), ("LOWER-LEDGER.json", ledgers), ("DOMAINS.json", domains)):
        typed.publish_or_match(args.input / name, value)
    report = {
        "schema": "N26-accepted-sharp-radius-conditional-partial-subtree-force-forest-v1",
        "verified": True, "radius_scope": typed.SCOPE, "radius_upper": str(radius),
        "source_conditional_acceptance_sha256": manifest["source_conditional_acceptance_sha256"],
        "original_U_pending_subtrees_unchanged": len(original["pending_states"]),
        "source_conditional_pending_subtrees": len(baseline["pending_states"]),
        "partial_source_roots_independently_reconstructed": len(results),
        "new_strict_radius_conditional_whole_partial_subtrees_excluded": frontier["new_sharp_partial_whole_subtrees_excluded"],
        "retained_attempted_partial_roots": sum(not row["whole_partial_transport_subtree_excluded_for_radius_at_most_Rstar"] for row in results),
        "retained_attempted_partial_closed_OPEN_boxes": sum(len(row["closed_OPEN_boxes"]) for row in pending),
        "all_unattempted_unclosed_siblings_and_shared_boundaries_preserved": True,
        "independent_center_BFS_and_anchor_Floyd_agree_with_all_pairs_Bellman_Ford": True,
        "independent_closed_leaf_boxes_agree_with_exact_force_tree_replay": True,
        "whole_subtree_exclusions_use_only_already_present_rods_and_no_future_faces": True,
        "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "conditional_frontier_families": frontier["families"],
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "original_U_frontier_nodes_removed": 0,
        "force_positive_controls": controls, "negative_controls_rejected": negatives,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: sha(args.input / name) for name in
                  ["MANIFEST.json", *manifest["copied_files"], "RSTAR-COMPETITOR-FRONTIER.json",
                   "CLASSIFICATION.json", "PENDING-PARTIAL-ANGLES.json", "LOWER-LEDGER.json", "DOMAINS.json"]},
        "source_files": digests, "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_sharp_partial_forest.py"]:
        raise ValueError("partial forest executed a different sealed verifier")
    for text, digest in digests.items():
        if sha(local_path(text)) != digest:
            raise ValueError("partial forest sources changed during replay")
    for name, digest in manifest["copied_files"].items():
        if sha(args.input / name) != digest:
            raise ValueError("partial forest sealed bytes changed during replay")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
