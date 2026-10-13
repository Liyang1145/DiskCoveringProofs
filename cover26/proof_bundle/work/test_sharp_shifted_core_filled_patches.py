"""Independent full source reconstruction and exact sharp-shifted controls.

Not a source geometry/current acceptance. Written continuous mathematics
remains explicitly bound, rather than inferred from finite controls.
"""

from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json
from math import comb
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
import n26_force as force
from n26_midarc_filled_patches import independent_disk_gate
import n26_sharp_shifted_core_filled_patches as rule
import n26_six_target_filled_ears as family
import verify_conditional_force_stage as binding


NEED = {3: 8, 4: 8, 5: 6, 6: 5, 7: 4, 8: 3}
COS = {3: F(24, 25), 4: F(22, 25), 5: F(3, 4),
       6: F(29, 50), 7: F(3, 8), 8: F(37, 250)}


def independent_patch_list(row):
    """Flood from LAST anchor across nonperimeter edges; independent filtering."""
    b = row["B"]
    faces = [tuple(i for i in range(row["next"]) if mask & (1 << i))
             for mask in row["faces"]]
    incident = defaultdict(list)
    for index, face in enumerate(faces):
        for edge in combinations(face, 2):
            incident[edge].append(index)
    result = []
    for size in (3, 4, 5, 6, 7, 8):
        for start in range(b):
            owners = [(start+j) % b for j in range(size)]
            cycle = {tuple(sorted((owners[j], owners[(j+1) % size]))) for j in range(size)}
            chain = [tuple(sorted((owners[j], owners[j+1]))) for j in range(size-1)]
            chord = tuple(sorted((owners[0], owners[-1])))
            if not incident[chord] or any(len(incident[edge]) != 1 for edge in chain):
                continue
            todo = [incident[chain[-1]][0]]
            selected = set(todo)
            while todo:
                index = todo.pop()
                for edge in combinations(faces[index], 2):
                    if edge in cycle:
                        continue
                    for neighbor in incident[edge]:
                        if neighbor not in selected:
                            selected.add(neighbor)
                            todo.append(neighbor)
            chosen = [row["faces"][i] for i in sorted(selected)]
            vertices = set().union(*(set(faces[i]) for i in selected))
            enclosed = sorted(v for v in vertices if v >= b)
            available = sum(v not in enclosed for v in range(b, 26))
            if vertices.intersection(range(b)) != set(owners) or available >= NEED[size]:
                continue
            edges = independent_disk_gate(b, chosen, owners)
            if edges is None:
                continue
            result.append({
                "consecutive_original_boundary_owners": owners, "outer_cycle_length": size,
                "actual_patch_face_indices": sorted(selected), "actual_patch_faces": chosen,
                "actual_enclosed_nonowner_labels": enclosed,
                "maximum_all_original_nonowner_slots_outside": available,
                "required_DISTINCT_ORIGINAL_outside_nonowners": NEED[size],
                "exact_patch_vertices": len(vertices), "exact_patch_edges": edges,
                "exact_patch_faces": len(chosen),
                "proper_subset_of_present_faces": len(selected) < len(faces),
            })
    return result


def independent_algebra(scan):
    u = F(234701, 1000000)
    r, q = 1-2*u, u*u
    if rule.REQUIRED != NEED or rule.COSINE_LOWER != COS:
        raise ValueError("producer changed the independently stated continuous theorem")
    # Derive all six cosine polynomials from the UNIVERSAL Chebyshev recurrence.
    cheb = [{0: F(1)}, {1: F(1)}]
    for n in range(1, 6):
        nxt = defaultdict(F)
        for power, coefficient in cheb[-1].items():
            nxt[power+1] += 2*coefficient
        for power, coefficient in cheb[-2].items():
            nxt[power] -= coefficient
        cheb.append({power: value for power, value in nxt.items() if value})
    expected = {
        1: {0: 1}, 2: {0: 1, 1: -2}, 3: {0: 1, 1: -4},
        4: {0: 1, 1: -8, 2: 8}, 5: {0: 1, 1: -12, 2: 16},
        6: {0: 1, 1: -18, 2: 48, 3: -32},
    }
    for n in range(1, 7):
        expanded = defaultdict(F)
        for power, coefficient in cheb[n].items():
            if power % 2 != n % 2:
                raise ValueError("cosine recurrence changed parity")
            exponent = power//2
            for j in range(exponent+1):
                expanded[j] += coefficient*comb(exponent, j)*(-1)**j
        if {j: c for j, c in expanded.items() if c} != expected[n]:
            raise ValueError("universal sharp-cosine polynomial recurrence differs")
    # Independently expand the universal circle-footprint square identity,
    # in X=d^2, Y=s^2, Z=t^2; no sampled d/s/t is used.
    def square(linear):
        result = defaultdict(F)
        for left, a in linear.items():
            for right, b in linear.items():
                result[tuple(x+y for x, y in zip(left, right))] += a*b
        return result
    lhs = square({(1, 0, 0): 1, (0, 1, 0): 1, (0, 0, 1): -1})
    lhs[(1, 1, 0)] -= 4
    lhs[(1, 0, 1)] += 4
    rhs = square({(1, 0, 0): 1, (0, 1, 0): -1, (0, 0, 1): 1})
    if {key: val for key, val in lhs.items() if val} != {
        key: val for key, val in rhs.items() if val
    }:
        raise ValueError("universal footprint-square identity differs")
    out = {}
    for k in NEED:
        n = k-2
        polynomial = sum(F(c)*q**j for j, c in expected[n].items())
        if n % 2:
            if polynomial <= 0 or (1-q)*polynomial**2 <= COS[k]**2:
                raise ValueError("independent positive radical cosine comparison failed")
        elif polynomial <= COS[k]:
            raise ValueError("independent rational cosine comparison failed")
        produced = scan["exact_sharp_arc_continuous_disk_AND_target_inequalities"][str(k)]
        if k in (3, 4):
            center, radius = ((F(-1, 40), F(1, 2)) if k == 3
                              else (F(-3, 50), F(47, 100)))
            margins = (r-abs(center)-radius, radius-2*u, COS[k]-2*u-center-radius)
            if min(margins) <= 0 or produced["exact_target_disk_center"] != [str(center), "0"]:
                raise ValueError("independent continuous target-disk inequalities failed")
            if (
                produced["exact_target_disk_radius"] != str(radius)
                or produced["exact_core_containment_radial_margin"] != str(margins[0])
                or produced["exact_radius_margin_above_two_U"] != str(margins[1])
                or produced["exact_patch_to_target_horizontal_margin_above_U"] != str(margins[2])
            ):
                raise ValueError("producer changed an exact continuous target-disk margin")
            out[str(k)] = {"outside_disks_required": 8, "exact_disk_margins": list(map(str, margins))}
            continue
        raw = {
            5: [("-1/50", "0"), ("9/40", "53/125"), ("9/40", "-53/125"),
                ("-53/200", "53/125"), ("-53/200", "-53/125"), ("-51/100", "0")],
            6: [("0", "0"), ("0", "1/2"), ("0", "-1/2"), ("-43/100", "1/4"),
                ("-43/100", "-1/4")],
            7: [("-1/10", "13/25"), ("-1/10", "-13/25"),
                ("-19/40", "47/200"), ("-19/40", "-47/200")],
            8: [("-161/500", "421/1000"), ("-161/500", "-421/1000"), ("-53/100", "0")],
        }[k]
        points = [(F(x), F(y)) for x, y in raw]
        maxnorm = max(x*x+y*y for x, y in points)
        separation = min((a[0]-b[0])**2+(a[1]-b[1])**2 for a, b in combinations(points, 2))
        margin = COS[k]-2*u-max(x for x, y in points)
        if maxnorm >= r*r or separation <= 4*u*u or margin <= 0 or len(points) != NEED[k]:
            raise ValueError("independent exact shifted-point geometry failed")
        if (
            produced["exact_target_points"] != [[str(x), str(y)] for x, y in points]
            or produced["exact_maximum_squared_target_norm"] != str(maxnorm)
            or produced["exact_minimum_squared_pair_distance"] != str(separation)
            or produced["exact_patch_to_target_horizontal_margin_above_U"] != str(margin)
        ):
            raise ValueError("producer target arithmetic differs from independent rational geometry")
        out[str(k)] = {"outside_disks_required": NEED[k],
                       "exact_pair_margin": str(separation-4*u*u),
                       "exact_core_squared_margin": str(r*r-maxnorm),
                       "exact_horizontal_margin": str(margin)}
    return out


def main():
    output = Path("outputs/n26-SIX-frontier-sharp-shifted-core-independent-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    scan_path = Path("outputs/n26-SIX-frontier-sharp-shifted-core-mathematical-scan-v1.json")
    scan = binding.read(scan_path)
    digests = {**scan["input_sha256"], **{
        linux(path): binding.sha(path) for path in (
            scan_path, Path(__file__), Path(force.__file__),
            Path("outputs/n26-new-scope-v1/CONSTANTS.json"), Path(family.__file__))}}
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("sharp shifted scan input changed before independent controls")
    exact = independent_algebra(scan)
    family.family_gate(binding.read(Path("outputs/n26-new-scope-v1/CONSTANTS.json")))
    source = binding.read(Path("outputs/n26-current28-six-target-source-geometry-v1/FRONTIER.json"))
    references = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
                  for b in (14, 15, 16, 17)}
    for reference in references.values():
        reference.children = lru_cache(None)(reference.children)
    records = {item["actual_SIX_source_index"]: item for item in scan["results"]}
    if len(records) != len(scan["results"]):
        raise ValueError("sharp shifted scan duplicated prefix ownership")
    matched, seen, cases, modes = [], set(), 0, Counter()
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("actual SIX source duplicates a prefix")
        seen.add(key)
        ref = references[row["B"]]
        state = ref.resolve(key[1])
        if {"B": row["B"], **ref.entry(key[1], state, ref.children(state))} != row:
            raise ValueError("entire original SIX source-prefix reconstruction differs")
        patches = independent_patch_list(row)
        if bool(patches) != (index in records):
            raise ValueError("independent sharp shifted classification differs")
        if patches:
            selected = max(patches, key=lambda item: (
                item["required_DISTINCT_ORIGINAL_outside_nonowners"]
                - item["maximum_all_original_nonowner_slots_outside"], -item["outer_cycle_length"]))
            item = records[index]
            if (
                row["terminal"] or item["actual_source_state"] != row
                or item["all_qualifying_filled_patches"] != patches
                or item["selected_strongest_filled_patch"] != selected
            ):
                raise ValueError("independent sharp shifted topology/source ownership differs")
            inside = set(selected["actual_enclosed_nonowner_labels"])
            outside = set(range(row["B"], 26))-inside
            need = NEED[selected["outer_cycle_length"]]
            by_original, by_shadow = Counter(), Counter()
            for m in range(row["B"]+9, 27):
                for originals in combinations(range(row["B"], 26), m-row["B"]):
                    available = len(outside.intersection(originals))
                    if available >= need:
                        raise ValueError("an original physical-disk case permits the necessary outsiders")
                    by_original[(m, available)] += 1
                for shadows in combinations(range(row["B"], 26), 26-m):
                    by_shadow[(m, len(outside-set(shadows)))] += 1
            if by_original != by_shadow:
                raise ValueError("independent original-subset/shadow-complement counts differ")
            cases += sum(by_original.values())
            matched.append(index)
            modes[str(selected["outer_cycle_length"])] += 1
        if (index+1) % 500 == 0:
            print(json.dumps({"actual_SIX_prefixes_independently_reconstructed": index+1,
                              "qualifying_whole_prefixes": len(matched),
                              "original_and_shadow_cases": cases, "formal_payments": 0}), flush=True)
    if any((b, prefix[:n]) in seen for b, prefix in seen for n in range(len(prefix))):
        raise ValueError("actual SIX source ownership overlaps ancestor and descendant")
    rejected = []
    def reject(name, action):
        try:
            action()
        except ValueError:
            rejected.append(name)
        else:
            raise AssertionError("invalid sharp shifted control accepted: "+name)
    for k in NEED:
        reject(str(k)+":nonstrict-quarter", lambda k=k: rule.target_gate(k, u=F(1, 4)))
        if k in (3, 4):
            reject(str(k)+":radius-equals-two-U",
                   lambda k=k: rule.target_gate(k, disk_radius=2*rule.U))
            reject(str(k)+":target-disk-outside-core",
                   lambda k=k: rule.target_gate(k, disk_center=F(-1)))
            reject(str(k)+":patch-accessible-target-disk",
                   lambda k=k: rule.target_gate(k, disk_center=F(0)))
            reject(str(k)+":finite-points-substituted-for-circle",
                   lambda k=k: rule.target_gate(k, points=[]))
        else:
            pts = rule.target_points(k)
            reject(str(k)+":duplicate-point",
                   lambda k=k, pts=pts: rule.target_gate(k, points=pts[:-1]+pts[:1]))
            reject(str(k)+":point-outside-core",
                   lambda k=k, pts=pts: rule.target_gate(k, points=[(F(2), F(0))]+pts[1:]))
            reject(str(k)+":inaccessible-condition-lost",
                   lambda k=k, pts=pts: rule.target_gate(k, points=[(F(1, 2), F(0))]+pts[1:]))
    exemplar = records[matched[0]]["selected_strongest_filled_patch"]
    owners, masks = exemplar["consecutive_original_boundary_owners"], exemplar["actual_patch_faces"]
    b = records[matched[0]]["B"]
    for name, changed, cycle in (
        ("missing-face", masks[1:], owners),
        ("duplicate-face", masks+masks[:1], owners),
        ("wrong-outer-cycle", masks, owners[:-1]+[(owners[-1]+2) % b]),
    ):
        if independent_disk_gate(b, changed, cycle) is not None:
            raise AssertionError("invalid filled patch accepted: "+name)
        rejected.append("topology:"+name)
    if len(rejected) != 29:
        raise ValueError("independent sharp shifted negative-control inventory changed")
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("sharp shifted source/code/proof changed during independent reconstruction")
    if len(matched) != scan["qualifying_whole_prefixes"] or dict(modes) != scan["selected_outer_cycle_length_counts"]:
        raise ValueError("independent sharp shifted totals differ")
    report = {
        "schema": "N26-SIX-frontier-sharp-shifted-core-independent-mathematical-controls-v1",
        "verified": False, "input_sha256": digests,
        "entire_actual_SIX_source_prefixes_independently_reconstructed": len(source["pending_states"]),
        "independent_qualifying_whole_prefixes": len(matched),
        "independent_family_counts": dict(Counter(str(source["pending_states"][i]["B"]) for i in matched)),
        "independent_selected_outer_cycle_length_counts": dict(modes),
        "all_original_physical_count_AND_shadow_complement_cases_checked": cases,
        "universal_cosine_recurrence_polynomial_identities_independently_expanded": 6,
        "universal_circle_footprint_square_identity_independently_expanded": True,
        "independent_exact_continuous_disk_and_shifted_target_margins": exact,
        "actual_invalid_geometry_and_topology_controls_rejected": rejected,
        "all_raw_complete_terminals_retained": True,
        "additional_beyond_queued_old_midarc_NOT_admitted":
            scan["additional_beyond_queued_old_midarc_NOT_admitted"],
        "prospective_frontier_NOT_current": len(source["pending_states"])-len(matched),
        "NEW_geometry_own_publication_current_AND_final_STILL_required": True,
        "candidate_whole_roots_removed": 0, "new_formal_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("input_sha256", "independent_exact_continuous_disk_and_shifted_target_margins",
                                     "actual_invalid_geometry_and_topology_controls_rejected")}), flush=True)


if __name__ == "__main__":
    main()
