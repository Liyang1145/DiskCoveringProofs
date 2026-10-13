"""Distinct preserved old92/NEW134rod arithmetic forest, NOT geometry admission.

Pure arithmetic inputs only. No typed context, diagnostic producer or source
history cache is imported. Geometry callers must replay the entire actual
latest original model/source/history through their own frozen interface.
"""

from copy import deepcopy
from fractions import Fraction as F

import n26_extended_signed_support_forest as old
import n26_full134rod_correlated_quadratic_energy as correlated


KIND = "FULL134-CORRELATED-ENERGY"
KINDS = (*old.KINDS, KIND)
MAX_FULL_SUPPORTS = 64
SUPPORT_MODE = "DISTINCT-ALL34FACE-134ROD-CORRELATED-SUPPORT"


def model_gate(original):
    return correlated.full.model_gate(
        original["data"][0], original["reference"], original["data"][3])


def full_support_gate(model, supports):
    if not isinstance(supports, list) or not 1 <= len(supports) <= MAX_FULL_SUPPORTS:
        raise ValueError("mixed full134rod forest has no explicit bounded NEW support table")
    kernels = []
    for item in supports:
        if (not isinstance(item, dict)
                or set(item) != {"mode", "kernel_certificate", "suggestion_point_turns"}
                or item["mode"] != SUPPORT_MODE
                or not isinstance(item["suggestion_point_turns"], list)
                or len(item["suggestion_point_turns"]) != 15):
            raise ValueError("mixed full134rod table relabels an old or unknown support mode")
        list(map(F, item["suggestion_point_turns"]))
        kernels.append(correlated.full.kernel_gate(model, item["kernel_certificate"]))
    return kernels


def partition(matrix, row, nodes, contractor, breadth_first):
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("mixed full134rod forest has no entire closed partition")
    view = []
    for node in nodes:
        if not isinstance(node, dict) or node.get("kind") not in KINDS:
            raise ValueError("mixed full134rod forest has an unknown actual proof mode")
        # This is ONLY a partition/old-proof inspection view. No NEW134rod
        # energy or kernel ever enters an old92rod proof backend.
        view.append({"kind": "OPEN"} if node["kind"] == KIND else deepcopy(node))
    leaves = old.partition(matrix, row, view, contractor, breadth_first)
    for leaf in leaves:
        if nodes[leaf["index"]]["kind"] == KIND:
            leaf["kind"] = KIND
    return leaves


def replay(original, original_kernel, arcs, row, nodes, old_supports, full_supports):
    model = model_gate(original)
    kernels = full_support_gate(model, full_supports)
    dfs = partition(original["matrix"], row, nodes, old.prior.prior.tighten, False)
    bfs = partition(original["matrix"], row, nodes, old.prior.prior.independently_contract, True)
    if dfs != bfs:
        raise ValueError("mixed full134rod independent closed partitions disagree")
    view = [{"kind": "OPEN"} if node["kind"] == KIND else deepcopy(node) for node in nodes]
    previous, provisional, ledger = old.replay(
        original, original_kernel, arcs, row, view, old_supports)
    new_indices = {leaf["index"] for leaf in dfs if leaf["kind"] == KIND}
    pending = [leaf for leaf in provisional if leaf["index"] not in new_indices]
    used, margins = set(), []
    for leaf in dfs:
        if leaf["kind"] != KIND:
            continue
        node = nodes[leaf["index"]]
        if set(node) != {"kind", "full_support_index", "certificate"}:
            raise ValueError("mixed NEW134rod leaf has unknown or missing proof fields")
        index = node["full_support_index"]
        if type(index) is not int or not 0 <= index < len(kernels):
            raise ValueError("mixed NEW134rod leaf names an invalid distinct support")
        result = correlated.bound(
            kernels[index], original["matrix"], leaf["lower"], leaf["upper"],
            node["certificate"], original["radius"], arcs)
        if (result["arithmetic_strict_target_test_passed"] is not True
                or F(result["strict_energy_margin"]) <= 0
                or F(result["strict_radius_margin"]) <= 0):
            raise ValueError("mixed NEW134rod leaf lacks an exact strict WHOLE closed-leaf bound")
        used.add(index)
        margins.append(F(result["strict_radius_margin"]))
        ledger.append({**leaf, "full_support_index": index,
                       "certificate": node["certificate"], "arithmetic_result": result})
    counts = {kind: sum(node["kind"] == kind for node in nodes) for kind in KINDS}
    if counts["SPLIT"]+1 != len(dfs):
        raise ValueError("mixed full134rod forest lost a complete closed sibling")
    return {
        **previous, "nodes": len(nodes), "counts": counts,
        "all_original92rod_proof_modes_and_original_LOCAL_preserved_distinctly": True,
        "all_complete34face_and_native76vertex_source_identities_checked": True,
        "NEW_full134rod_supports_checked": len(kernels),
        "NEW_full134rod_supports_used_by_strict_closed_leaves": sorted(used),
        "NEW_full134rod_correlated_leaves_exactly_reconstructed": len(new_indices),
        "minimum_NEW_full134rod_strict_radius_margin": str(min(margins)) if margins else None,
        "arithmetic_entire_root_lower_bound_cover_completed": not pending,
        "arithmetic_entire_root_strictly_empty": not pending and counts["LOCAL"] == 0,
        "retained_OPEN_leaves": len(pending),
        "NEW134rod_never_relabelled_as_original92rod_or_same92alternative": True,
        "verified": False, "new_geometric_payments": 0,
        "complete_latest_source_model_history_geometry_admission_still_required": True,
    }, pending, sorted(ledger, key=lambda leaf: leaf["index"])


def retention_gate(seed, record):
    if (len(record["nodes"]) < len(seed["nodes"])
            or record["alternative_supports"][:len(seed["alternative_supports"])] != seed["alternative_supports"]
            or record["full134rod_supports"][:len(seed.get("full134rod_supports", []))] != seed.get("full134rod_supports", [])
            or any(node["kind"] != "OPEN" and node != record["nodes"][index]
                   for index, node in enumerate(seed["nodes"]))):
        raise ValueError("mixed full134rod continuation reset old nodes or either support prefix")
    old_ledger = {leaf["index"]: leaf for leaf in seed["arithmetic_ledger"]}
    ledger = {leaf["index"]: leaf for leaf in record["arithmetic_ledger"]}
    if (len(old_ledger) != len(seed["arithmetic_ledger"]) or len(ledger) != len(record["arithmetic_ledger"])
            or any(ledger.get(index) != leaf for index, leaf in old_ledger.items())):
        raise ValueError("mixed full134rod continuation changed a previously proved closed-leaf ledger")
    return len(seed["nodes"]), len(seed["alternative_supports"]), len(old_ledger)
