"""READ-ONLY mathematical/implementation audit of exact26 basic source interfaces.

Freshly checks all bound copies of ten core implementations, the continuous
base/multi-slope area tables, every actual pending state's original topology,
degree/rod/angle interfaces and the qualified imported cardinality implication.
Writes only a NEW audit report, never frozen ledgers or current acceptance.
Advanced candidate models and final unrestricted joint closure stay pending.
"""

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
import json
from pathlib import Path

from audit_prefix_partition import linux
import audit_prefix_origin as origin
import audit_prefix_partition as combinatorics
import n26_force as force
import n26_force_angles as force_angles
import new_upper_scope as family
import n26_generic_position_universal_polynomials as generic
import n26_embedded_dual_bridge_algebra as bridge
import n26_unit_cap_universal_identities as cap
import test_embedded_dual_bridge_algebra as independent_bridge
import verify_conditional_force_stage as binding
import verify_degree_area as degree
import verify_force_forest as forest
import verify_force_stage as stages
import verify_multislope_area as multi
import verify_partial_area_closures as partial


MODULES = (
    force, force_angles, degree, multi, partial, forest, origin, combinatorics, stages, family,
)
CURRENT_SHA = "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
FINAL_SHA = "7c2d29f19f310de58d03a2043fae3dde8bcaeb69635843086118a91ab9b6db4e"
IMPORT_SHA = "418bc6fed59559180f0badd216fbc2ea52123a99db9aaa93d94799a95fc9ce53"
IMPORT_FINAL_SHA = "b5de48b774945328aecb75705c3aa26ad9e57a05da970d30b50f3d1ad989bbb7"


def snapshot_gate(current, final, imported, imported_final):
    if (
        current["schema"] != "N26-complete-current-with-six-target-source-geometry-audit-v1"
        or current["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or current["candidate_angle_unresolved_closed_boxes"] != 25
        or current["radius_scope"] != binding.SCOPE
        or final["current_audit_sha256"] != CURRENT_SHA
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(current["files"])
        or imported["verified"] is not True or imported_final["verified"] is not True
        or imported_final["import_own_acceptance_sha256"] != IMPORT_SHA
        or imported_final["all_actual_imported_dependency_content_independently_rehashed"] is not True
        or imported_final["actual_full_imported_dependency_count"] != 555503
        or imported_final["imported_theorem_scope_is_qualified_prior_SOURCE_NOT_a_new_old_tree_replay"] is not True
        or imported_final["original_missing_binding_creator_terminal_qualification_preserved"] is not True
        or imported_final["exact_original_cardinality_implication_under_imported_prior_theorem"][
            "every_at_most26_cover_in_scope_has_EXACTLY26_original_distinct_necessary_disks"] is not True
        or any(record[field] is not False for record in (current, final, imported, imported_final)
               for field in ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("core interface audit lost actual accepted proof-time snapshot/qualified cardinality scope")


def module_inventory(current):
    modules = {Path(module.__file__).name: module for module in MODULES}
    copies = defaultdict(list)
    for text, digest in current["files"].items():
        name = binding.local_path(text).name
        if name in modules:
            copies[name].append((text, digest))
    if set(copies) != set(modules):
        raise ValueError("actual current omitted a core interface implementation")
    results, paths = {}, []
    for name in sorted(copies):
        actual = binding.sha(modules[name].__file__)
        variants = {digest for text, digest in copies[name]}
        if variants != {actual}:
            raise ValueError("a bound core implementation is not the audited unchanged version: " + name)
        for text, digest in copies[name]:
            if binding.sha(text) != digest:
                raise ValueError("core bound implementation changed: " + text)
            paths.append(binding.local_path(text))
        paths.append(Path(modules[name].__file__))
        results[name] = {
            "bound_copies_freshly_rehashed": len(copies[name]),
            "distinct_bound_implementation_versions": len(variants),
            "actual_audited_loaded_sha256": actual,
            "all_bound_paths": [text for text, digest in copies[name]],
        }
    return results, paths, copies


def find_area_bundles(current, copies, name, schema):
    found, seen = [], set()
    for text, digest in copies[name]:
        folder = binding.local_path(text).parent
        # Later actual packages retain the original base acceptance under its
        # HONEST bound BASE-ACCEPTANCE filename, not as their own VERIFIED.
        for filename in ("VERIFIED.json", "BASE-ACCEPTANCE.json", "AREA-ACCEPTANCE.json"):
            accepted_path = folder / filename
            key = linux(accepted_path)
            if key in seen or current["files"].get(key) is None:
                continue
            accepted = binding.read(accepted_path)
            if accepted.get("schema") != schema:
                continue
            certificate_path = folder / "CERTIFICATE.json"
            if current["files"].get(linux(certificate_path)) != accepted["files"].get("CERTIFICATE.json"):
                continue
            if accepted["verified"] is not True or binding.sha(accepted_path) != current["files"][key]:
                raise ValueError("accepted area bundle bytes changed")
            seen.add(key)
            found.append((folder, accepted_path, accepted))
    if not found:
        raise ValueError("actual current has no accepted " + schema + " source")
    return sorted(found, key=lambda row: linux(row[1]))


def source_state_gate(row, state, refs):
    b, prefix = row["B"], tuple(row["prefix"])
    reference = refs[b]
    if {"B": b, **reference.entry(prefix, state, reference.children(state))} != row:
        raise ValueError("actual ORIGINAL pending state differs from complete prefix reconstruction")
    bounds = partial.degree_bounds(state, b)
    if len(bounds) != 26 or any(not (2 if i < b else 3) <= lo <= hi <= 25
                                for i, (lo, hi) in enumerate(bounds)):
        raise ValueError("partial degree domain is not a conservative original26 degree interface")
    spec = {"N": 26, "B": b, "next": state.next_vertex, "faces": list(state.faces)}
    vertices, rods = force.rod_graph(spec)
    if (
        vertices != b + state.next_vertex + len(state.faces)
        or len(rods) != 2*b + 3*len(state.faces)
        or any(not 0 <= left < vertices or not 0 <= right < vertices or left == right
               for left, right in rods)
    ):
        raise ValueError("partial anchor/common-witness rod interpretation changed")
    matrix = force.angular_domain(spec)
    lo, hi = force.rootbox(matrix)
    if any(a > z or z-a >= F(1, 2) for a, z in zip(lo, hi)):
        raise ValueError("necessary rotation-normalized anchor domain changed")
    windows = multi.angle_rows(b, state.adjacency)
    # Translate the independently bitset-derived gap masks back into anchor
    # differences. Every such inequality must be present in the BFS/Floyd
    # matrix. Stronger Floyd consequences are allowed.
    for mask, encoded_cap in windows:
        members = [i for i in range(b) if mask >> i & 1]
        start = next(i for i in members if not (mask >> ((i-1) % b) & 1))
        end = start
        while mask >> ((end+1) % b) & 1:
            end = (end+1) % b
        left, right = (start-1) % b, end
        wrap = int(right < left)
        if F(matrix[left][right], force.D) > F(encoded_cap, force.D)-wrap:
            raise ValueError("bitset area angle window is not implied by actual BFS/Floyd domain")
    complete_degrees = None
    if row["terminal"]:
        edges = origin.validate_disk(26, b, row["faces"])
        boundary_counts, interior_counts = degree.degrees(b, row["faces"])
        actual_degrees = [value.bit_count() for value in state.adjacency]
        if (
            edges != 75-b or len(row["faces"]) != 50-b
            or sum(actual_degrees) != 150-2*b
            or sum(boundary_counts) != b or sum(interior_counts) != 26-b
            or bounds != tuple((value, value) for value in actual_degrees)
            or len(rods) != 150-b or vertices != 76
        ):
            raise ValueError("complete genuine26 dual/degree/full-rod interface changed")
        complete_degrees = actual_degrees
    return {
        "B": b, "prefix": list(prefix), "actual_faces": len(state.faces),
        "introduced_original_vertices": state.next_vertex,
        "rod_vertices": vertices, "necessary_rods": len(rods),
        "necessary_graph_angle_windows": len(windows),
        "complete_original_degrees": complete_degrees,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("read-only interface audit requires a fresh report")
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    final_path = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")
    imported_path = Path("outputs/n26-imported-n25-source-premise-v1/VERIFIED.json")
    imported_final_path = Path("outputs/n26-imported-n25-source-premise-independent-final-v1.json")
    paths = [current_path, final_path, imported_path, imported_final_path]
    if [binding.sha(path) for path in paths] != [CURRENT_SHA, FINAL_SHA, IMPORT_SHA, IMPORT_FINAL_SHA]:
        raise ValueError("actual completed proof-time pairs changed")
    current, final, imported, imported_final = [binding.read(path) for path in paths]
    snapshot_gate(current, final, imported, imported_final)
    inventory_results, bound_paths, copies = module_inventory(current)
    paths.extend(bound_paths)
    print(json.dumps({
        "exact26_core_bound_modules_freshly_checked": len(inventory_results),
        "actual_bound_copies": sum(value["bound_copies_freshly_rehashed"] for value in inventory_results.values()),
        "all_versions_match_inspected_unchanged_implementations": True,
    }), flush=True)
    base_bundles = find_area_bundles(
        current, copies, "verify_degree_area.py", "N26-Voronoi-degree-boundary-arc-strict-area-lower-v1")
    multi_bundles = find_area_bundles(
        current, copies, "verify_multislope_area.py", "N26-area-and-graph-angle-rational-dual-lower-v1")
    # Recompute each DISTINCT continuous certificate. Equal coefficient-table
    # bytes in different accepted graph sources are not distinct arithmetic.
    base_results, base_cache, base_certificates = [], {}, {}
    arcs = force.load_trig()[0]
    family_constants_path = Path("outputs/n26-new-scope-v1/CONSTANTS.json")
    rational_upper_path = Path("outputs/n26-rational-upper-v1/VERIFIED.json")
    for selected in (family_constants_path, rational_upper_path):
        if current["files"].get(linux(selected)) != binding.sha(selected):
            raise ValueError("actual original owner-family/continuous-upper premise not bound")
    original_family_result = family.gate(
        binding.read(family_constants_path), binding.read(rational_upper_path), arcs,
    )
    paths.extend((family_constants_path, rational_upper_path))
    for folder, accepted_path, accepted in base_bundles:
        path = folder / "CERTIFICATE.json"
        if current["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("actual base area certificate not bound")
        cert = binding.read(path)
        degree.parameter_gate(cert)
        # SOURCE hash selects graphs, not the continuous envelope calculation.
        signature_data = {key: value for key, value in cert.items()
                          if key not in ("source_sha256", "full_catalog_complete", "global_optimality_proved")}
        signature = json.dumps(signature_data, sort_keys=True, separators=(",", ":"))
        if signature not in base_cache:
            maxima, internal, bins, infeasible = degree.derive_tables(cert, arcs, progress=True)
            degree.table_claim_gate(cert, maxima, internal)
            base_cache[signature] = (maxima, internal, bins, infeasible)
        maxima, internal, bins, infeasible = base_cache[signature]
        degree.table_claim_gate(cert, maxima, internal)
        base_certificates[accepted["files"]["CERTIFICATE.json"]] = cert
        base_results.append({
            "actual_bound_area_source": linux(folder),
            "actual_bound_acceptance_file": linux(accepted_path),
            "certificate_sha256": binding.sha(path),
            "all8192_CLOSED_continuous_bins_recomputed": True,
            "all24_boundary_and_interior_degree_coefficients_outward_verified": True,
            "infeasible_gap_bins": infeasible,
        })
        paths.extend((path, accepted_path))
    multi_results, multi_cache = [], {}
    for folder, accepted_path, accepted in multi_bundles:
        old_path, path = folder / "CERTIFICATE.json", folder / "MULTISLOPE-CERTIFICATE.json"
        for selected in (old_path, path):
            if current["files"].get(linux(selected)) != binding.sha(selected):
                raise ValueError("actual multi-slope continuous inputs not bound")
        old, cert = binding.read(old_path), binding.read(path)
        degree.parameter_gate(old)
        multi.parameter_gate(cert)
        signature = json.dumps({
            "old": {key: value for key, value in old.items() if key != "source_sha256"},
            "slopes": cert["slopes"],
        }, sort_keys=True, separators=(",", ":"))
        if signature not in multi_cache:
            multi_cache[signature] = multi.derive_tables(old, arcs, progress=True)
        multi.table_claim_gate(cert, multi_cache[signature])
        multi_results.append({
            "actual_bound_multi_slope_source": linux(folder),
            "actual_bound_acceptance_file": linux(accepted_path),
            "certificate_sha256": binding.sha(path),
            "all8192_CLOSED_continuous_bins_and_16_GLOBAL_supports_recomputed": True,
            "all24_boundary_degree_support_coefficients_outward_verified": True,
        })
        paths.extend((old_path, path, accepted_path))
    six_folder = Path("outputs/n26-current28-six-target-source-geometry-v1")
    certificates = {
        "cap": binding.read(six_folder / "UNIT-CAP-CERTIFICATE.json"),
        "generic": binding.read(six_folder / "GENERIC-CERTIFICATE.json"),
        "bridge": binding.read(six_folder / "EMBEDDED-CORNER-CERTIFICATE.json"),
    }
    fresh_algebra = {
        "cap": cap.gate(certificates["cap"]), "generic": generic.gate(certificates["generic"]),
        "bridge": bridge.gate(certificates["bridge"]),
        "independent_bridge_scalar_identities": independent_bridge.independent_identities(certificates["bridge"]),
    }
    source_path = binding.local_path(current["current_frontier_actual_file"])
    source = binding.read(source_path)
    if (
        current["files"].get(linux(source_path)) != binding.sha(source_path)
        or len(source["pending_states"]) != 5637
        or source["radius_scope"] != binding.SCOPE
        or source["families"] != current["Rstar_conditional_frontier_families"]
    ):
        raise ValueError("core interface audit replaced actual5637 proof-time pending source")
    refs = {b: origin.OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
            for b in (14, 15, 16, 17)}
    for ref in refs.values():
        ref.children = lru_cache(None)(ref.children)
    seen, topology, terminals, degree_windows = set(), [], [], 0
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("actual core pending-source ownership duplicated")
        seen.add(key)
        state = refs[row["B"]].resolve(key[1])
        result = source_state_gate(row, state, refs)
        topology.append(result)
        degree_windows += result["necessary_graph_angle_windows"]
        if row["terminal"]:
            terminals.append(result)
        if (index+1) % 1000 == 0:
            print(json.dumps({
                "actual_original26_pending_source_interfaces_reconstructed": index+1,
                "of": len(source["pending_states"]),
            }), flush=True)
    if any((b, prefix[:length]) in seen for b, prefix in seen for length in range(len(prefix))):
        raise ValueError("actual source has ancestor/descendant overlap")
    if len(terminals) != sum(row["terminal"] for row in source["pending_states"]):
        raise ValueError("a raw original terminal vanished")
    # Fresh exact cardinality inequality, not a rounded decimal comparison.
    u = F(234701, 1000000)
    threshold = F(3, 2)*(1-u*u)
    if not (threshold > 0 and threshold*threshold > 2 and u < F(1, 4)
            and 1-4*u > 0 and F(current["r_strict_interval"][1]) < u):
        raise ValueError("qualified original26/no-exposed-origin/radius implication failed")
    negatives = []
    from copy import deepcopy
    for name, index, field, value in (
        ("wrong-proof-time-source-promoted-to-U", 0, "radius_scope", "unconditional-original-U"),
        ("uncompleted-prior-import-final", 3, "all_actual_imported_dependency_content_independently_rehashed", False),
        ("prior-import-qualification-hidden", 3, "imported_theorem_scope_is_qualified_prior_SOURCE_NOT_a_new_old_tree_replay", False),
        ("global-optimality-overclaim", 0, "global_optimality_proved", True),
    ):
        changed = deepcopy([current, final, imported, imported_final])
        changed[index][field] = value
        try:
            snapshot_gate(*changed)
        except ValueError:
            negatives.append(name)
        else:
            raise AssertionError("bad actual interface scope accepted")
    exemplar = source["pending_states"][0]
    state = refs[exemplar["B"]].resolve(tuple(exemplar["prefix"]))
    changed = deepcopy(exemplar)
    changed["next"] += 1
    try:
        source_state_gate(changed, state, refs)
    except ValueError:
        negatives.append("changed-actual-original-state-not-merely-degree-count")
    else:
        raise AssertionError("changed source state accepted")
    paths.extend((
        source_path, Path(__file__), Path(cap.__file__), Path(generic.__file__),
        Path(bridge.__file__), Path(independent_bridge.__file__),
        six_folder / "UNIT-CAP-CERTIFICATE.json", six_folder / "GENERIC-CERTIFICATE.json",
        six_folder / "EMBEDDED-CORNER-CERTIFICATE.json",
        Path("work/n26-exact26-core-native-source-interface-proof.md"),
        Path("work/n26-exact26-original-voronoi-interface-proof.md"),
        Path("work/n26-unit-cap-domination-and-no-return-proof.md"),
        Path("work/n26-embedded-dual-and-corner-starring-bridge-proof.md"),
        Path("work/n26-degree-area-proof.md"), Path("work/n26-multislope-area-proof.md"),
        Path("work/n26-partial-area-proof.md"), Path("work/n26-force-forest-proof.md"),
        Path("work/n26-angular-closure-proof.md"), Path("work/n26-conditional-force-stage-proof.md"),
    ))
    distinct = {linux(path): path for path in paths}
    digests = {text: binding.sha(path) for text, path in distinct.items()}
    for text, value in digests.items():
        if text in current["files"] and current["files"][text] != value:
            raise ValueError("actual bound core audit input changed during arithmetic replay: " + text)
    for module in MODULES:
        if binding.sha(module.__file__) != inventory_results[Path(module.__file__).name][
            "actual_audited_loaded_sha256"]:
            raise ValueError("loaded core audit implementation changed during arithmetic replay")
    if [binding.sha(path) for path in (current_path, final_path, imported_path, imported_final_path)] != [
        CURRENT_SHA, FINAL_SHA, IMPORT_SHA, IMPORT_FINAL_SHA,
    ]:
        raise ValueError("actual completed proof-time pairs changed during core audit")
    report = {
        "schema": "N26-exact26-core-original-geometry-source-interface-audit-v1",
        "verified": False, "new_formal_geometric_payments": 0,
        "actual_completed_SIX_and_qualified_prior_import_pairs_used": True,
        "proof_time_current_sha256": CURRENT_SHA,
        "proof_time_source_frontier": 5637, "candidate_angle_roots_NOT_original_disk_count": 25,
        "qualified_original_physical_disk_count": 26,
        "all_actual_bound_core_implementation_copies_freshly_rehashed": inventory_results,
        "complete_base_area_envelope_recomputations": base_results,
        "complete_multi_slope_envelope_recomputations": multi_results,
        "fresh_universal_algebra": fresh_algebra,
        "fresh_original_family_bound_with_explicit_imported_n8": original_family_result,
        "entire5637_ORIGINAL_pending_states_degree_rod_angle_interfaces_reconstructed": True,
        "all_current_source_states": topology, "all_raw_complete_terminals_retained": terminals,
        "total_independently_checked_graph_angle_windows": degree_windows,
        "exact_positive_original_cardinality_threshold": str(threshold),
        "exact_original_cardinality_square_margin_above_two": str(threshold*threshold-2),
        "exact_exposed_center_origin_gap_at_U": str(1-4*u),
        "actual_scope_negative_controls_rejected": negatives,
        "prior_import_full_content_acceptance_REUSED_NOT_555503_content_checks_repeated_here": True,
        "written_continuous_core_interface_NOT_machine_geometry_proof_from_finite_checks": True,
        "candidate_specific_extended_models_and_other_historical_payments_STILL_require_individual_full_source_audit": True,
        "native_kernel_variants_and_all_actual_payment_dispatches_NOT_claimed_fully_audited_here": True,
        "full_unrestricted_joint_source_geometry_current_AND_final_STILL_required": True,
        "current_formal_frontier_NOT_updated_by_this_audit": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "input_sha256": digests,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "actual_exact26_core_interface_audit_completed_NOT_current_acceptance": True,
        "actual_bound_core_copies": sum(value["bound_copies_freshly_rehashed"]
                                      for value in inventory_results.values()),
        "full_original_pending_source_states": 5637,
        "base_area_sources": len(base_results), "multi_slope_sources": len(multi_results),
        "new_formal_geometric_payments": 0, "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
