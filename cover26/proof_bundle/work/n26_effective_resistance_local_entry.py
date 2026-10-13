"""NEW92-rod harmonic-resistance LOCAL arithmetic; not source admission.

No typed context or diagnostic producer is imported. The caller supplies a
separately reconstructed actual model, and must still perform full latest
source/model/history geometry admission before any formal payment.
"""

from fractions import Fraction as F
from functools import lru_cache

import verify_refined_anchor_pinning as original_pin
import n26_candidate_curvature_energy as energy


SCHEMA = "N26-distinct-original92rod-effective-resistance-LOCAL-entry-v1"
ALLOWANCE = F(7,800000)
base = original_pin.base


def prepare(original, root, records, path, local, reference, inverse):
    if (
        reference["N"] != 26 or reference["B"] != 16
        or reference["radius_scope"] != "at-most-the-certified-same-root-Rstar"
        or F(local["unrestricted_center_neighbourhood_halfwidth_before_rotation"]) != ALLOWANCE
    ):
        raise ValueError("effective-resistance pinning changed the original92 model/LOCAL theorem")
    base.support_gate(reference,records,path)
    geometry,edges,_,t = base.root_geometry(original,root,records)
    if reference["edges"] != [list(edge) for edge in edges]:
        raise ValueError("effective-resistance pinning changed the actual positive source rods")
    kernel = energy.kernel_gate(reference,inverse)
    scale,den = kernel["scale"],kernel["inverse_denominator"]
    p = [[F(int(value),scale) for value in row] for row in reference["reference_numerators"]]
    weights = [F(value,scale) for value in kernel["weights"]]
    if len(p) != 62 or any(len(row) != 2 for row in p) or p[0] != [F(1),F(0)]:
        raise ValueError("effective-resistance rational reference changed the actual rotation gauge")
    gradients = [[F(0),F(0)] for _ in p]
    energy0 = F(0)
    for (u,v),weight in zip(edges,weights):
        difference = [p[u][axis]-p[v][axis] for axis in range(2)]
        energy0 += weight*sum(value*value for value in difference)
        for axis in range(2):
            gradients[u][axis] += weight*difference[axis]
            gradients[v][axis] -= weight*difference[axis]
    residuals = [sum(abs(value) for value in row) for row in gradients]
    path_resistance,parents = base.resistances(62,edges,weights)
    anchor_labels = []
    for vertex in range(16,62):
        current,seen = vertex,set()
        while current >= 16:
            if current in seen or parents[current] is None:
                raise ValueError("old comparison path is cyclic or disconnected")
            seen.add(current)
            current = parents[current]
        anchor_labels.append(current)
    resistance = [F(scale*kernel["inverse"][i][i],den) for i in range(46)]
    harmonic = [[F(value,den) for value in row] for row in kernel["harmonic"]]
    if (
        any(value <= 0 or value > path_resistance[16+i] for i,value in enumerate(resistance))
        or any(min(row) < 0 or sum(row) != 1 for row in harmonic)
    ):
        raise ValueError("actual effective resistance or harmonic convex-combination identity failed")
    radial,nonradial,constant = [],[],t[1]*sum(weights)-energy0
    for anchor in range(16):
        norm2 = sum(value*value for value in p[anchor])
        k = sum(a*b for a,b in zip(gradients[anchor],p[anchor]))/norm2
        if k <= 0:
            raise ValueError("effective-resistance pinning has a nonpositive radial coefficient")
        radial.append(k)
        nonradial.append(sum(abs(a-k*b) for a,b in zip(gradients[anchor],p[anchor])))
        constant += k*(norm2-1)
    roots = [base.sqrt_upper(value) for value in resistance]
    old_roots = [base.sqrt_upper(path_resistance[v]) for v in range(16,62)]
    K = 2*sum(residuals[16+i]*value for i,value in enumerate(roots))
    old_K = 2*sum(residuals[16+i]*value for i,value in enumerate(old_roots))
    rounding = [
        base.sqrt_upper(sum(max(abs(a-point),abs(b-point))**2
                            for (a,b),point in zip(geometry[16+i],p[16+i])))
        for i in range(26)
    ]
    return {
        "schema":SCHEMA,"kernel":kernel,"geometry":geometry,"reference":reference,
        "points":p,"weights":weights,"edges":edges,"residuals":residuals,
        "radial":radial,"nonradial":nonradial,"constant":constant,
        "effective_resistance":resistance,"harmonic":harmonic,
        "sqrt_effective_resistance":roots,"old_sqrt_path_resistance":old_roots,
        "old_path_resistance":path_resistance,"old_path_parents":parents,
        "old_path_anchor_labels":anchor_labels,"K":K,"old_K":old_K,
        "center_reference_rounding":rounding,"allowed":ALLOWANCE,
        "arithmetic_preparation_NOT_complete_current_source_or_geometry_model_admission":True,
    }


@lru_cache(maxsize=20000)
def endpoint(turn):
    return base.endpoint(turn)


def arc_errors(prepared,cells):
    if len(cells) != 15:
        raise ValueError("effective-resistance LOCAL domain changed the15-anchor frame")
    boxes = [[base.iv.point(1),base.iv.point(0)]]
    quarters = ((F(0),(1,0)),(F(1,4),(0,1)),(F(1,2),(-1,0)),
                (F(3,4),(0,-1)),(F(1),(1,0)))
    for index,row in enumerate(cells,1):
        lo,hi = map(F,row)
        if not 0 < lo < hi < 1 or hi-lo >= F(1,4):
            raise ValueError("effective-resistance domain is not an original short canonical root-containing arc")
        a,b = endpoint(lo),endpoint(hi)
        if (
            base.geo.ivcross(a,prepared["geometry"][index])[0] <= 0
            or base.geo.ivcross(prepared["geometry"][index],b)[0] <= 0
        ):
            raise ValueError("effective-resistance angle hull omitted the exact root")
        values = [a,b]
        values.extend([[base.iv.point(x),base.iv.point(y)] for turn,(x,y) in quarters if lo <= turn <= hi])
        boxes.append([(min(point[axis][0] for point in values),
                       max(point[axis][1] for point in values)) for axis in range(2)])
    return [
        base.sqrt_upper(sum(max(abs(a-x),abs(b-x))**2
                            for (a,b),x in zip(box,point)))
        for box,point in zip(boxes,prepared["points"][:16])
    ]


def evaluate(prepared,cells):
    if (
        prepared["schema"] != SCHEMA or prepared["allowed"] != ALLOWANCE
        or prepared["kernel"].get("original_candidate_92_rod_46_free_vertex_kernel") is not True
        or len(prepared["harmonic"]) != 46
    ):
        raise ValueError("effective-resistance evaluation changed its explicit model or original LOCAL width")
    errors = arc_errors(prepared,cells)
    beta = [sum(weight*error for weight,error in zip(row,errors)) for row in prepared["harmonic"]]
    old_beta = [errors[anchor] for anchor in prepared["old_path_anchor_labels"]]
    anchor_charge = sum(k*epsilon**2+2*s*epsilon for k,s,epsilon in
                        zip(prepared["radial"],prepared["nonradial"],errors))
    A = prepared["constant"]+anchor_charge+2*sum(
        prepared["residuals"][16+i]*value for i,value in enumerate(beta))
    old_A = prepared["constant"]+anchor_charge+2*sum(
        prepared["residuals"][16+i]*value for i,value in enumerate(old_beta))
    K,old_K = prepared["K"],prepared["old_K"]
    A0 = max(A,F(0))
    Y = (K+base.sqrt_upper(K*K+4*A0))/2
    old_Y = old_K+base.sqrt_upper(max(old_A,F(0)))
    if Y < 0 or Y*Y-K*Y < A0:
        raise AssertionError("effective-resistance outward quadratic root did not bound displacement energy")
    center_errors = [
        beta[i]+prepared["sqrt_effective_resistance"][i]*Y+prepared["center_reference_rounding"][i]
        for i in range(26)
    ]
    old_center_errors = [
        old_beta[i]+prepared["old_sqrt_path_resistance"][i]*old_Y+prepared["center_reference_rounding"][i]
        for i in range(26)
    ]
    actual,old = max(center_errors),max(old_center_errors)
    return {
        "schema":SCHEMA,"verified":False,"new_geometric_payments":0,
        "actual_closed_root_containing_anchor_cells":cells,
        "all46_grounded_effective_resistances_checked_against_explicit_paths":True,
        "no_actual_realization_harmonicity_or_center_neighbourhood_assumed":True,
        "exact_unit_circle_radial_identity_and_individual_anchor_errors_retained":True,
        "individual_anchor_errors":list(map(str,errors)),
        "individual_free_harmonic_anchor_error_bounds":list(map(str,beta)),
        "reference_energy_slack_A":str(A),"internal_residual_coefficient_K":str(K),
        "sqrt_displacement_energy_upper":str(Y),
        "quadratic_root_outward_margin":str(Y*Y-K*Y-A0),
        "all26_original_center_error_bounds":list(map(str,center_errors)),
        "maximum_original_center_error_upper":str(actual),
        "unchanged_original52_coordinate_LOCAL_allowance":str(ALLOWANCE),
        "strict_original_LOCAL_entry_margin":str(ALLOWANCE-actual),
        "arithmetic_entire_closed_box_enters_original_LOCAL":actual < ALLOWANCE,
        "same_cells_old_path_pin_maximum_center_error_upper":str(old),
        "same_cells_old_path_pin_enters_original_LOCAL":old < ALLOWANCE,
        "old_path_error_minus_new_harmonic_error":str(old-actual),
        "LOCAL_equality_region_NOT_declared_empty":True,
        "full_actual_latest_source_model_history_geometry_admission_STILL_required":True,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
    }
