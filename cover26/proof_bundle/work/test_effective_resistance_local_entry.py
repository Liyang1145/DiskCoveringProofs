"""Independent exact harmonic-resistance identities and LOCAL calculations.

Rebuilds the actual original model; no producer/typed context is imported.
Fresh independent edge-energy and inverse-coordinate square completions plus
scalar LOCAL recomputation for every actual calibration/positive witness.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_effective_resistance_local_entry as harmonic
import verify_conditional_force_stage as binding


CURRENT_SHA = "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
SEED_SHA = "4914725c65f3995014a30484f2e4a37428701efe02bbed2edce98f70d96626cc"


def exact_quadratic(matrix,vector):
    return sum(vector[i]*value*vector[j] for i,row in enumerate(matrix)
               for j,value in enumerate(row) if value)


def resistance_identity_controls(prepared):
    kernel = prepared["kernel"]
    scale,den = kernel["scale"],kernel["inverse_denominator"]
    # Independently form rational G by direct free edge incidence, NOT by
    # taking the primary gate's stored Laplacian block.
    G = [[F(0) for _ in range(46)] for _ in range(46)]
    for (u,v),weight in zip(prepared["edges"],prepared["weights"]):
        for vertex in (u,v):
            if vertex >= 16:
                G[vertex-16][vertex-16] += weight
        if u >= 16 and v >= 16:
            G[u-16][v-16] -= weight
            G[v-16][u-16] -= weight
    checks,sharp,minimum_margin = 0,0,None
    z = [F((7*i+3)%13-6,11) for i in range(46)]
    energy = exact_quadratic(G,z)
    if energy < 0:
        raise AssertionError("independent positive grounded edge form was negative")
    for vertex in range(46):
        u = [F(scale*kernel["inverse"][i][vertex],den) for i in range(46)]
        resistance = u[vertex]
        if resistance != prepared["effective_resistance"][vertex]:
            raise AssertionError("independent physical resistance has wrong rational scale")
        if [sum(value*x for value,x in zip(row,u)) for row in G] != [
                F(int(i==vertex)) for i in range(46)]:
            raise AssertionError("independent rational grounded inverse column identity failed")
        deviation = [value-z[vertex]*entry/resistance for value,entry in zip(z,u)]
        left = resistance*energy-z[vertex]**2
        right = resistance*exact_quadratic(G,deviation)
        if left != right or left < 0:
            raise AssertionError("independent coordinate-resistance square completion failed")
        # z=u is the actual sharp equality direction; a finite arbitrary
        # sample alone would not justify the stated resistance constant.
        if resistance*exact_quadratic(G,u)-u[vertex]**2 != 0:
            raise AssertionError("independent effective-resistance equality direction failed")
        checks += 1
        sharp += 1
        minimum_margin = left if minimum_margin is None else min(minimum_margin,left)
    anchors = [[F((3*i+1)%7-3,5),F((5*i+2)%11-5,7)] for i in range(16)]
    free = [[F((7*i+3)%13-6,11),F((11*i+4)%17-8,13)] for i in range(46)]
    points = anchors+free
    direct = sum(weight*sum((points[u][axis]-points[v][axis])**2 for axis in (0,1))
                 for (u,v),weight in zip(prepared["edges"],prepared["weights"]))
    extension = [[sum(F(kernel["harmonic"][i][j],den)*anchors[j][axis] for j in range(16))
                  for axis in (0,1)] for i in range(46)]
    residual = sum(exact_quadratic(G,[free[i][axis]-extension[i][axis] for i in range(46)])
                   for axis in (0,1))
    boundary = sum(F(weight,scale*den)*sum((anchors[i][axis]-anchors[j][axis])**2 for axis in (0,1))
                   for i,j,weight in kernel["pair_weights"])
    if direct != boundary+residual or min(boundary,residual) < 0:
        raise AssertionError("independent arbitrary nonunit-anchor/nonharmonic square completion failed")
    return {
        "all46_rational_ground_inverse_columns_reconstructed_from_direct_edges":checks,
        "all46_coordinate_resistance_square_completions":checks,
        "all46_sharp_resistance_equality_directions":sharp,
        "arbitrary_nonunit_two_coordinate_anchor_and_nonharmonic_free_identity":True,
        "minimum_actual_coordinate_Cauchy_margin":str(minimum_margin),
        "physical_rational_scale_not_integer_inverse_diagonal_used":True,
    }


def independent_result(prepared,cells):
    # Independent whole-arc envelope calls the preserved original exact
    # endpoint/quarter implementation, not NEW arc_errors.
    boxes = harmonic.original_pin.arc_boxes(cells,prepared["geometry"])
    epsilons = [
        harmonic.base.sqrt_upper(sum(max(abs(a-x),abs(b-x))**2
                                    for (a,b),x in zip(box,point)))
        for box,point in zip(boxes,prepared["points"][:16])
    ]
    points,weights,edges = prepared["points"],prepared["weights"],prepared["edges"]
    gradients = [[F(0),F(0)] for _ in points]
    E0 = F(0)
    for (u,v),weight in zip(edges,weights):
        for axis in (0,1):
            delta = points[u][axis]-points[v][axis]
            E0 += weight*delta*delta
            gradients[u][axis] += weight*delta
            gradients[v][axis] -= weight*delta
    r = [sum(abs(value) for value in row) for row in gradients]
    t_plus = prepared["reference_squared_radius_upper"]
    A = t_plus*sum(weights)-E0
    for i in range(16):
        norm2 = sum(value*value for value in points[i])
        k = sum(a*b for a,b in zip(gradients[i],points[i]))/norm2
        s = sum(abs(a-k*b) for a,b in zip(gradients[i],points[i]))
        A += k*(norm2-1+epsilons[i]**2)+2*s*epsilons[i]
    kernel,den = prepared["kernel"],prepared["kernel"]["inverse_denominator"]
    resistance = [F(kernel["scale"]*kernel["inverse"][i][i],den) for i in range(46)]
    rootR = [harmonic.base.sqrt_upper(value) for value in resistance]
    beta = [sum(F(weight,den)*epsilons[a] for a,weight in enumerate(row))
            for row in kernel["harmonic"]]
    A += 2*sum(r[i+16]*beta[i] for i in range(46))
    K = 2*sum(r[i+16]*rootR[i] for i in range(46))
    Y = (K+harmonic.base.sqrt_upper(K*K+4*max(A,F(0))))/2
    maximum = max(beta[i]+rootR[i]*Y+prepared["center_reference_rounding"][i] for i in range(26))
    return {"epsilons":epsilons,"beta":beta,"A":A,"K":K,"Y":Y,"maximum":maximum}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis",type=Path,required=True)
    parser.add_argument("--diagnosis-sha256",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve independent effective-resistance controls")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("independent harmonic controls lack the exact completed diagnostic")
    diagnosis = binding.read(args.diagnosis)
    if (
        diagnosis["schema"] != "N26-unaccepted-actual-original92rod-harmonic-LOCAL-strengthening-diagnostic-v1"
        or diagnosis["actual_proof_time_current_sha256"] != CURRENT_SHA
        or diagnosis["actual_root25v4_diagnosis_sha256"] != SEED_SHA
        or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
        or diagnosis["global_optimality_proved"] is not False
    ):
        raise ValueError("independent harmonic diagnostic changed original source/status")
    for text,digest in diagnosis["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("independent harmonic source input changed")
    reference = binding.read("outputs/n26-leaf-pinned-candidate-angles-v2/REFERENCE-PINNING.json")
    inverse = binding.read("outputs/n26-current-candidate-Dirichlet-overlay-v1/DIRICHLET-KERNEL.json")
    data = harmonic.base.source_gate(
        Path("outputs/n26-positive-stress-v1"),Path("outputs/n26-centered-local-barrier-v2"),
        Path("outputs/n26-candidate-transport-control-v1"),reference)
    prepared = harmonic.prepare(*data[:5],reference,inverse)
    # Only for independent scalar arithmetic, obtained again from exact root
    # geometry, not from the primary's stored A or K.
    prepared["reference_squared_radius_upper"] = harmonic.base.root_geometry(*data[:3])[3][1]
    identities = resistance_identity_controls(prepared)
    results,actual_improved = [],0
    witnesses = [item["result"] for item in diagnosis["calibration_actual_closed_root_hulls"]]
    witnesses.extend(item["result"] for item in diagnosis["actual_latest_OPEN_leaf_NEW_LOCAL_arithmetic_witnesses"])
    for number,result in enumerate(witnesses):
        cells = result["actual_closed_root_containing_anchor_cells"]
        independent = independent_result(prepared,cells)
        if (
            list(map(str,independent["epsilons"])) != result["individual_anchor_errors"]
            or list(map(str,independent["beta"])) != result["individual_free_harmonic_anchor_error_bounds"]
            or independent["A"] != F(result["reference_energy_slack_A"])
            or independent["K"] != F(result["internal_residual_coefficient_K"])
            or independent["Y"] != F(result["sqrt_displacement_energy_upper"])
            or independent["maximum"] != F(result["maximum_original_center_error_upper"])
        ):
            raise ValueError("independent entire-arc harmonic LOCAL arithmetic differs")
        proposal = deepcopy(reference)
        proposal["closed_anchor_angle_cells"] = cells
        old_passes = result["same_cells_old_path_pin_enters_original_LOCAL"]
        try:
            old = harmonic.original_pin.derive(*data[:5],proposal)
        except ValueError:
            if old_passes:
                raise ValueError("primary old-path comparison falsely passed original checker")
        else:
            if (
                old_passes is not True
                or F(old["maximum_center_to_exact_rotated_root_euclidean_error_upper"])
                != F(result["same_cells_old_path_pin_maximum_center_error_upper"])
            ):
                raise ValueError("primary old-path comparison differs from original actual checker")
        if result["arithmetic_entire_closed_box_enters_original_LOCAL"] and not old_passes:
            actual_improved += 1
        results.append({
            "witness_number":number,"maximum_harmonic_center_error_upper":str(independent["maximum"]),
            "new_LOCAL_passed":independent["maximum"] < harmonic.ALLOWANCE,
            "old_original_path_checker_passed":old_passes,
        })
        print(json.dumps({"independent_harmonic_LOCAL_witness":number+1,
                          "of":len(witnesses),"new_LOCAL":results[-1]["new_LOCAL_passed"]}),flush=True)
    negatives = []
    def reject(label,call):
        try:
            call()
        except (ValueError,KeyError,TypeError,IndexError,AssertionError):
            negatives.append(label)
        else:
            raise AssertionError("invalid effective-resistance control accepted: "+label)
    changed = deepcopy(inverse)
    changed["inverse_numerators"][0][0] = str(int(changed["inverse_numerators"][0][0])+1)
    reject("changed-exact-grounded-inverse",lambda:harmonic.energy.kernel_gate(reference,changed))
    changed_ref = deepcopy(reference)
    changed_ref["weight_numerators"][0] = "0"
    reject("nonpositive-necessary-rod-weight",lambda:harmonic.energy.kernel_gate(changed_ref,inverse))
    changed = {**prepared,"allowed":F(1,1000)}
    reject("original52_LOCAL_allowance-enlarged",lambda:harmonic.evaluate(changed,witnesses[0]["actual_closed_root_containing_anchor_cells"]))
    changed = {**prepared,"kernel":{**prepared["kernel"],"original_candidate_92_rod_46_free_vertex_kernel":False}}
    reject("full134rod-relabelled-as-original92",lambda:harmonic.evaluate(changed,witnesses[0]["actual_closed_root_containing_anchor_cells"]))
    cells = deepcopy(witnesses[0]["actual_closed_root_containing_anchor_cells"])
    cells[0] = ["0","1/2"]
    reject("long-arc-or-wrong-gauge-LOCAL",lambda:harmonic.evaluate(prepared,cells))
    cells = deepcopy(witnesses[0]["actual_closed_root_containing_anchor_cells"])
    cells[0] = ["1/1000","1/999"]
    reject("root-omitted-from-LOCAL-hull",lambda:harmonic.evaluate(prepared,cells))
    mutated = deepcopy(prepared)
    mutated["effective_resistance"][0] *= F(1,2)
    reject("understated-physical-effective-resistance",lambda:resistance_identity_controls(mutated))
    if actual_improved < diagnosis["new_closed_LOCAL_hulls_not_payable_by_old_path_bound"]:
        raise ValueError("independent harmonic arithmetic lost the claimed real strengthening")
    for text,digest in diagnosis["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("independent harmonic source changed during exact controls")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("harmonic producer evidence changed during independent check")
    inventory = {**diagnosis["input_sha256"],linux(args.diagnosis):args.diagnosis_sha256,
                 linux(__file__):binding.sha(__file__)}
    report = {
        "schema":"N26-independent-original92rod-effective-resistance-LOCAL-arithmetic-controls-v1",
        "verified":False,"new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "diagnosis_sha256":args.diagnosis_sha256,
        "fresh_actual_original_model_and_exact_inverse_reconstructed":True,
        "independent_ground_resistance_and_nonharmonic_square_completion":identities,
        "independent_entire_arc_scalar_LOCAL_witnesses":results,
        "actual_improved_hulls_new_LOCAL_old_original_path_checker_failed":actual_improved,
        "all_actual_newest_OPEN_leaf_positive_arithmetic_witnesses_independently_checked":
            len(diagnosis["actual_latest_OPEN_leaf_NEW_LOCAL_arithmetic_witnesses"]),
        "full984_negative_scan_NOT_independently_repeated_as_a_geometry_claim":True,
        "actual_rejection_controls_passed":negatives,
        "original52_coordinate_LOCAL_allowance_unchanged":"7/800000",
        "actual_latest_source_model_history_geometry_admission_AND_current_STILL_required":True,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_test_sha256":binding.sha(__file__),
    }
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "independent_effective_resistance_LOCAL_controls_completed_NOT_admission":True,
        "exact_coordinate_resistance_identities":46,"sharp_resistance_controls":46,
        "independent_closed_LOCAL_witnesses":len(results),"actual_improved_LOCAL_hulls":actual_improved,
        "actual_rejection_controls":len(negatives),"global_optimality_proved":False,
    }),flush=True)


if __name__ == "__main__":
    main()
