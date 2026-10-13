"""Independent original-rod, augmented-inverse and whole-domain arithmetic replay."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
import n26_b17_radial_origin_energy as radial
import n26_force as force
from n26_pairwise_affine_energy import pair_lines
import verify_conditional_force_stage as binding


def independently_build(spec, certificate):
    b, introduced, faces = spec["B"], spec["next"], spec["faces"]
    edges = [(i, b+i) for i in range(b)]+[(i, b+(i+1) % b) for i in range(b)]
    edges += [(b+introduced+k, b+i) for k, mask in enumerate(faces)
              for i in range(introduced) if mask & (1 << i)]
    vertices = b+introduced+len(faces)
    weights, scale = certificate["weight_numerators"], certificate["weight_scale"]
    mu, owner = certificate["origin_weight_numerator"], certificate["owner"]
    matrix = [[0]*vertices for _ in range(vertices)]
    for (u, v), w in zip(edges, weights):
        matrix[u][u] += w
        matrix[v][v] += w
        matrix[u][v] -= w
        matrix[v][u] -= w
    matrix[b+owner][b+owner] += mu
    count = vertices-b
    den = int(certificate["inverse_denominator"])
    inverse = [[int(v) for v in row] for row in certificate["inverse_numerators"]]
    for i in range(count):
        for j in range(count):
            if sum(matrix[b+i][b+k]*inverse[k][j] for k in range(count)) != (
                    den if i == j else 0):
                raise AssertionError("independent augmented inverse failed")
    h = [[-sum(inverse[i][k]*matrix[b+k][j] for k in range(count))
          for j in range(b)] for i in range(count)]
    schur = [[den*matrix[i][j]+sum(matrix[i][b+k]*h[k][j] for k in range(count))
              for j in range(b)] for i in range(b)]
    q = [sum(row) for row in schur]
    if (any(v < 0 for v in q) or any(min(row) < 0 or sum(row) > den for row in h)
            or any(schur[i][j] != schur[j][i] for i in range(b) for j in range(b))
            or any(schur[i][j] > 0 for i in range(b) for j in range(b) if i != j)):
        raise AssertionError("independent substochastic/Schur signs failed")
    # Different exact nonharmonic points and direct MATRIX Schur energy,
    # rather than copying the producer's pair/row-sum expansion.
    anchors = [[F((2*i+3) % 11-5, 3), F((7*i+1) % 13-6, 5)] for i in range(b)]
    free = [[F((5*i+2) % 17-8, 7), F((3*i+4) % 19-9, 11)] for i in range(count)]
    points = anchors+free
    direct = sum(F(w, scale)*sum((points[u][d]-points[v][d])**2 for d in range(2))
                 for (u, v), w in zip(edges, weights))
    direct += F(mu, scale)*sum(v*v for v in free[owner])
    boundary = sum(F(schur[i][j], scale*den)*sum(anchors[i][d]*anchors[j][d]
                   for d in range(2)) for i in range(b) for j in range(b))
    deviation = [[free[i][d]-sum(F(h[i][j], den)*anchors[j][d] for j in range(b))
                  for d in range(2)] for i in range(count)]
    residual = sum(F(matrix[b+i][b+j], scale)*sum(deviation[i][d]*deviation[j][d]
                   for d in range(2)) for i in range(count) for j in range(count))
    if direct != boundary+residual or residual < 0:
        raise AssertionError("independent nonunit-anchor square completion failed")
    # All unit anchors at (1,0) and all free points zero form a radius-one
    # rod realization satisfying EVERY inward-owner branch's radial bound.
    original_direct = F(sum(w for (u, v), w in zip(edges, weights)
                            if (u < b) != (v < b)), scale)
    inward_boundary = F(sum(q), scale*den)-F(mu, scale)*radial.KAPPA**2
    if not inward_boundary <= original_direct <= F(sum(weights), scale):
        raise AssertionError("radial energy falsely excludes a feasible radius-one control")
    return edges, schur, q, den


def independent_bound(spec, certificate, schur, q, den, matrix, affine, radius, arcs):
    b, weights = spec["B"], sum(certificate["weight_numerators"])
    additive = F(sum(q), den*weights)-F(certificate["origin_weight_numerator"], weights)*radial.KAPPA**2
    gradient, constant, index = [F(0)]*b, additive, 0
    for i in range(b):
        for j in range(i+1, b):
            if not schur[i][j]:
                continue
            a, c = -F(matrix[j][i], force.D), F(matrix[i][j], force.D)
            lines = pair_lines(a, c, arcs)
            mixture = affine["pair_line_mixture_numerators"][index]
            if len(mixture) != len(lines) or min(mixture) < 0 or not sum(mixture):
                raise AssertionError("independent affine mixture shape/sign failed")
            slope = sum(F(n, sum(mixture))*v[0] for n, v in zip(mixture, lines))
            intercept = sum(F(n, sum(mixture))*v[1] for n, v in zip(mixture, lines))
            coefficient = F(-schur[i][j], den*weights)
            gradient[i] -= coefficient*slope
            gradient[j] += coefficient*slope
            constant += coefficient*intercept
            index += 1
    if index != len(affine["pair_line_mixture_numerators"]):
        raise AssertionError("extra pair mixtures in independent replay")
    for i, j, n in affine["difference_dual_terms"]:
        if n < 0:
            raise AssertionError("negative independent domain dual")
        multiplier = F(n, affine["difference_dual_denominator"])
        gradient[i] -= multiplier
        gradient[j] += multiplier
        constant -= multiplier*F(matrix[i][j], force.D)
    support = constant
    for j, g in enumerate(gradient):
        lower, upper = F(-matrix[j][0], force.D), F(matrix[0][j], force.D)
        support += g*(lower if g >= 0 else upper)
    return support, support > F(radius)**2


def independently_close(matrix, owner):
    domain = [row[:] for row in matrix]
    if owner:
        domain[owner-1][owner] = min(domain[owner-1][owner], 450000)
    else:
        domain[16][0] = min(domain[16][0], -9550000)
    # Bellman shortest paths, rather than the producer's Floyd closure.
    result = []
    for source in range(17):
        distances = list(domain[source])
        for _ in range(16):
            updated = [min(distances[u]+domain[u][v] for u in range(17)) for v in range(17)]
            if updated == distances:
                break
            distances = updated
        result.append(distances)
    return None if any(result[j][j] < 0 for j in range(17)) else result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    record = binding.read(args.input)
    digests = dict(record["input_sha256"])
    digests[str(args.input)] = binding.sha(args.input)
    digests[__file__] = binding.sha(__file__)
    for text, sha in digests.items():
        if binding.sha(Path(text)) != sha:
            raise ValueError("radial pilot input changed before independent replay")
    current = binding.read(Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json"))
    radius = F(current["r_strict_interval"][1])
    arcs = force.load_trig(Path("outputs/n26-original-candidate-arithmetic-context-v1"))[0]
    reference = OriginReference(26, 17, "dfs", caps=force.CAPS, scale=force.D)
    kernels, branches, positive_gains, all_excluded = 0, 0, 0, 0
    negative_controls = []
    for row in record["results"]:
        source = row["actual_source_state"]
        prefix = tuple(source["prefix"])
        state = reference.resolve(prefix)
        if source != {"B": 17, **reference.entry(prefix, state, reference.children(state))}:
            raise AssertionError("independent actual source reconstruction failed")
        spec = row["actual_partial_spec"]
        matrix, strict_or_empty = force.angular_domain(spec), 0
        if sorted(b["owner"] for b in row["branches"]) != list(range(17)):
            raise AssertionError("independent replay lacks complete17branch union")
        for branch in row["branches"]:
            domain = independently_close(matrix, branch["owner"])
            if domain is None:
                if not branch["branch_angular_domain_empty"]:
                    raise AssertionError("independent empty branch mismatch")
                strict_or_empty += 1
                continue
            if branch["branch_angular_domain_empty"]:
                raise AssertionError("producer deleted a nonempty radial branch")
            certificate = branch["radial_kernel_certificate"]
            edges, schur, q, den = independently_build(spec, certificate)
            _, base_schur, base_q, base_den = independently_build(
                spec, branch["baseline_zero_origin_kernel_certificate"])
            if (certificate["owner"] != branch["owner"] or len(edges) != 91
                    or sum(q) <= 0 or any(base_q)):
                raise AssertionError("actual91rod radial/zero-origin model association failed")
            turns = list(map(F, branch["exact_feasible_anchor_turns"]))
            if any(turns[j]-turns[i] > F(domain[i][j], force.D)
                   for i in range(17) for j in range(17)):
                raise AssertionError("independent exact point violates an actual branch domain")
            def point(s, row_sums, inverse_den, cert):
                weight_sum = sum(cert["weight_numerators"])
                lower = F(sum(row_sums), inverse_den*weight_sum)-F(
                    cert["origin_weight_numerator"], weight_sum)*radial.KAPPA**2
                upper_sine = lower
                for i in range(17):
                    for j in range(i+1, 17):
                        if not s[i][j]:
                            continue
                        coefficient = F(-s[i][j], inverse_den*weight_sum)
                        cosine = arcs.sincos_turn(turns[j]-turns[i])[0]
                        sine = arcs.sincos_turn((turns[j]-turns[i])/2)[1]
                        lower += coefficient*F(2*(arcs.SCALE-cosine[1]), arcs.SCALE)
                        upper_sine += coefficient*F(4*max(v*v for v in sine), arcs.SCALE**2)
                if lower > upper_sine:
                    raise AssertionError("independent sine-square outward point control failed")
                return lower
            actual_point = point(schur, q, den, certificate)
            baseline_point = point(base_schur, base_q, base_den, branch["baseline_zero_origin_kernel_certificate"])
            if (actual_point != F(branch["exact_fixed_point_lower"])
                    or baseline_point != F(branch["baseline_exact_fixed_point_lower"])):
                raise AssertionError("independent exact fixed point mismatch")
            gain = F(branch["exact_fixed_point_radial_gain_over_identical_rod_weights"])
            if not gain <= actual_point-baseline_point or gain <= 0:
                raise AssertionError("independent strict radial gain failed")
            bound, strict = independent_bound(
                spec, certificate, schur, q, den, domain, branch["whole_branch_affine_certificate"], radius, arcs)
            reported = branch["whole_branch_exact_result"]
            if (bound != F(reported["normalized_radial_branch_entire_domain_energy_lower"])
                    or strict != reported["arithmetic_strict_entire_radial_branch"]):
                raise AssertionError("independent whole-domain bound/strictness mismatch")
            branches += 1
            kernels += 2
            positive_gains += 1
            strict_or_empty += strict
            if not negative_controls:
                mutations = []
                for name in ("old-schema", "wrong-owner", "wrong-kappa", "negative-origin",
                             "zero-original-rod", "false-inverse", "wrong-inverse-size", "forged-harmonic-flag"):
                    changed = deepcopy(certificate)
                    if name == "old-schema":
                        changed["schema"] = radial.partial.SCHEMA
                    elif name == "wrong-owner":
                        changed["owner"] = 17
                    elif name == "wrong-kappa":
                        changed["kappa"] = "1"
                    elif name == "negative-origin":
                        changed["origin_weight_numerator"] = -1
                    elif name == "zero-original-rod":
                        changed["weight_numerators"][0] = 0
                    elif name == "false-inverse":
                        changed["inverse_numerators"][0][0] = str(int(changed["inverse_numerators"][0][0])+1)
                    elif name == "wrong-inverse-size":
                        changed["inverse_numerators"].pop()
                    else:
                        changed["distinct_full134rod_60free_positive_candidate_kernel"] = True
                    mutations.append((name, changed))
                for name, changed in mutations:
                    try:
                        radial.kernel_gate(spec, changed)
                    except (ValueError, ArithmeticError):
                        negative_controls.append(name)
                    else:
                        raise AssertionError("radial gate accepted negative control "+name)
        if (strict_or_empty == 17) != row["arithmetic_all17branches_strict_or_empty"]:
            raise AssertionError("independent all17branches exclusion mismatch")
        all_excluded += strict_or_empty == 17
    for text, sha in digests.items():
        if binding.sha(Path(text)) != sha:
            raise ValueError("radial pilot input changed during independent replay")
    report = {
        "schema": "N26-B17-origin-energy-independent-arithmetic-controls-v1",
        "verified": False, "pilot_sha256": digests[str(args.input)], "input_sha256": digests,
        "independent_original_rod_graph_augmented_ground_kernels_checked": kernels,
        "independent_entire_radial_branch_bounds_checked": branches,
        "exact_positive_fixed_point_radial_gains_independently_checked": positive_gains,
        "independent_complete17branch_covers_excluded": all_excluded,
        "actual_negative_model_and_inverse_controls_rejected": negative_controls,
        "scalar_pair_line_lemmas_reused_NOT_independently_reproved": True,
        "independent_nonunit_anchor_matrix_square_completion_and_sine_square_controls": True,
        "nonzero_Schur_row_sums_and_original_rod_only_radius_cap_preserved": True,
        "source_geometry_admission_NOT_performed": True,
        "source_forests_histories_ledgers_UNMODIFIED": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: report[key] for key in (
        "independent_original_rod_graph_augmented_ground_kernels_checked",
        "independent_entire_radial_branch_bounds_checked",
        "exact_positive_fixed_point_radial_gains_independently_checked",
        "independent_complete17branch_covers_excluded",
        "actual_negative_model_and_inverse_controls_rejected")}), flush=True)


if __name__ == "__main__":
    main()
