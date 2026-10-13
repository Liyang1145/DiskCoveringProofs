"""Distinct whole-domain correlated energy for actual origin-cover branches.

Only scalar Taylor/support lemmas are reused. No old134-only kernel flag or
W-only radius budget is forged; the exact origin constant and W+mu remain.
"""

from fractions import Fraction as F
from math import isqrt

import n26_full134rod_two_origin_kernel as origin
import n26_full134rod_correlated_quadratic_energy as scalar


SCHEMA = "N26-distinct-full134rod-origin-branch-correlated-certificate-v1"


def kernel_scope(kernel):
    mu = F(kernel["origin_multiplier"])
    W = F(kernel["original_physical_rod_weight_sum"])
    R = F(kernel["original_physical_ground_resistance"])
    if (
        kernel["schema"] != origin.SCHEMA or kernel["B"] != 16
        or kernel["vertices"] != 76 or kernel["physical_rods"] != 134
        or kernel["actual_eligible_origin_center_labels"] != [16,25]
        or kernel["origin_center_label"] not in (16,25)
        or not 0 <= mu <= 10**60 or W <= 0 or R <= 0
        or kernel["radius_squared_budget_weight"] != W+mu
        or kernel["boundary_origin_constant"] != mu/(1+mu*R)
        or kernel["augmented_integer_inverse_identity_all3600_entries_checked"] is not True
        or kernel.get("distinct_full134rod_60free_positive_candidate_kernel") is not None
        or kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None
        or kernel["energy_denominator"] <= 0
    ):
        raise ValueError("origin whole-domain bound changed its distinct kernel/constant/radius budget")
    pairs,seen = kernel["pairs"],set()
    for i,j,weight in pairs:
        if not 0 <= i < j < 16 or (i,j) in seen or type(weight) is not int or weight <= 0:
            raise ValueError("origin whole-domain bound has invalid positive Schur pairs")
        seen.add((i,j))


def combined_minorant(kernel,matrix,reference,lower,upper,arcs,parts):
    kernel_scope(kernel)
    if type(parts) is not int or not 1 <= parts <= 256:
        raise ValueError("origin Taylor strips need an explicit positive bounded integer")
    ref,lo,hi,_,_ = scalar.full.hull.hull_gate(reference,lower,upper,matrix)
    combined,total = [[F(0)]*15 for _ in range(15)],F(0)
    for index in range(parts):
        a,b = F(index,parts),F(index+1,parts)
        weight = 2*(b-a)-(b*b-a*a)
        left,right = [],[]
        for r,x,y in zip(ref[1:],lo[1:],hi[1:]):
            values = [r+t*(endpoint-r) for t in (a,b) for endpoint in (x,y)]
            left.append(min(values))
            right.append(max(values))
        minorant = scalar.full.hull.quadratic.hessian_minorant(kernel,matrix,left,right,arcs)
        for i in range(15):
            for j in range(15):
                combined[i][j] += weight*minorant[i][j]
        total += weight
    if total != 1 or any(combined[i][j] != combined[j][i] for i in range(15) for j in range(15)):
        raise AssertionError("origin whole-domain normalized Taylor weights or symmetry failed")
    return combined


def quadratic_data(kernel,matrix,lower,upper,certificate,arcs):
    kernel_scope(kernel)
    fields = {"schema","origin_center_label","origin_multiplier","reference_turns","parts",
              "curvature_correction","quadratic_support_point","difference_dual"}
    if (
        set(certificate) != fields or certificate["schema"] != SCHEMA
        or type(certificate["origin_center_label"]) is not int
        or certificate["origin_center_label"] != kernel["origin_center_label"]
        or F(certificate["origin_multiplier"]) != kernel["origin_multiplier"]
    ):
        raise ValueError("origin correlated certificate changed its source owner/multiplier/mode")
    ref,lo,hi,_,_ = scalar.full.hull.hull_gate(certificate["reference_turns"],lower,upper,matrix)
    correction,point = list(map(F,certificate["curvature_correction"])),list(map(F,certificate["quadratic_support_point"]))
    if (
        len(correction) != 15 or len(point) != 15
        or any(type(value) is bool for key in ("curvature_correction","quadratic_support_point")
               for value in certificate[key])
        or any(not 0 <= value <= 10**60 for value in correction)
        or any(abs(value) > 10**60 for value in point)
    ):
        raise ValueError("origin correlated correction/tangent data invalid")
    dual = certificate["difference_dual"]
    if (
        set(dual) != {"q","terms"} or type(dual["q"]) is not int or not 0 < dual["q"] <= 10**60
        or not isinstance(dual["terms"],list)
        or any(not isinstance(term,list) or len(term) != 3 or type(term[2]) not in (str,int)
               for term in dual["terms"])
    ):
        raise ValueError("origin correlated nonnegative difference dual fields invalid")
    minorant = combined_minorant(
        kernel,matrix,certificate["reference_turns"],lower,upper,arcs,certificate["parts"])
    error_allowance = F(15,scalar.full.hull.quadratic.ROUND_GRID)
    Q = [[value+(correction[i]-error_allowance if i == j else 0)
          for j,value in enumerate(row)] for i,row in enumerate(minorant)]
    pivots = scalar.full.hull.quadratic.positive_ldl(Q)
    a,b = [x-r for x,r in zip(lo[1:],ref[1:])],[y-r for y,r in zip(hi[1:],ref[1:])]
    point_lower,gradient = scalar.full.hull.outward_point_values(kernel,ref,arcs)
    # The scalar helper returns the PAIR energy only. The exact nonzero
    # origin Schur-row constant is explicitly restored before any comparison.
    energy = point_lower+kernel["boundary_origin_constant"]
    gradient_error = sum((high-low)/2*max(abs(x),abs(y))
                         for (low,high),x,y in zip(gradient[1:],a,b))
    linear = [(low+high)/2-eta*(x+y)/2
              for (low,high),eta,x,y in zip(gradient[1:],correction,a,b)]
    constant = sum(eta*x*y/2 for eta,x,y in zip(correction,a,b))-gradient_error
    return {
        "reference":ref,"lower":lo,"upper":hi,"lower_delta":a,"upper_delta":b,
        "quadratic":Q,"linear":linear,"constant":constant,
        "reference_energy_lower":energy,"support_point":point,
        "gradient_error":gradient_error,"rounding_operator_allowance":error_allowance,
        "minimum_LDL_pivot":min(pivots),
    }


def bound(kernel,matrix,lower,upper,certificate,radius,arcs):
    data = quadratic_data(kernel,matrix,lower,upper,certificate,arcs)
    support,controls = scalar.correlated_support(data,matrix,certificate["difference_dual"])
    lower_energy = data["reference_energy_lower"]+support
    budget = kernel["radius_squared_budget_weight"]
    upper_energy = F(radius)**2*budget
    square,grid = max(F(0),lower_energy)/budget,10**100
    radius_lower = F(isqrt(square.numerator*grid*grid//square.denominator),grid)
    if not radius_lower**2 <= square < (radius_lower+F(1,grid))**2:
        raise AssertionError("origin branch outward radius conversion failed")
    return {
        "schema":"N26-origin-branch-whole-closed-domain-correlated-result-v1",
        "origin_center_label":kernel["origin_center_label"],
        "origin_multiplier":str(kernel["origin_multiplier"]),
        "boundary_origin_constant":str(kernel["boundary_origin_constant"]),
        "physical134rod_weight_sum":str(kernel["original_physical_rod_weight_sum"]),
        "radius_squared_budget_W_PLUS_mu":str(budget),
        "boundary_origin_branch_energy_lower":str(lower_energy),
        "same_root_origin_branch_energy_upper":str(upper_energy),
        "strict_energy_margin":str(lower_energy-upper_energy),
        "strict_radius_margin":str(radius_lower-F(radius)),
        "arithmetic_strict_entire_origin_branch":lower_energy > upper_energy and radius_lower > F(radius),
        "all_closed_Taylor_strips_and_normalized_weights_checked":certificate["parts"],
        "rounding_operator_error_charged":str(data["rounding_operator_allowance"]),
        "exact_positive_LDL_minimum_pivot":str(data["minimum_LDL_pivot"]),
        "outward_gradient_interval_error_charged":str(data["gradient_error"]),
        "nonzero_origin_constant_AND_virtual_radius_budget_both_retained":True,
        "no_original134_only_or_original92_kernel_flag_forged":True,
        **controls,"verified":False,"new_geometric_payments":0,
        "both_origin_branches_STILL_required_for_a_whole_leaf":True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed":True,
    }


def suggest(kernel,matrix,lower,upper,reference,radius,arcs,parts=8):
    # Numerical choices are reusable heuristics, never source/model proofs.
    import n26_balanced_correlated_diagonal_suggestion as numerical
    minorant = combined_minorant(kernel,matrix,reference,lower,upper,arcs,parts)
    corrections,choices = numerical.correction_suggestion(minorant,lower,upper)
    data,selected,strategy = None,None,None
    for label,diagonal in corrections:
        certificate = {
            "schema":SCHEMA,"origin_center_label":kernel["origin_center_label"],
            "origin_multiplier":str(kernel["origin_multiplier"]),
            "reference_turns":list(map(str,reference)),"parts":parts,
            "curvature_correction":list(map(str,diagonal)),
            "quadratic_support_point":["0"]*15,"difference_dual":{"q":1,"terms":[]},
        }
        try:
            candidate = quadratic_data(kernel,matrix,lower,upper,certificate,arcs)
        except ValueError:
            continue
        data,selected,strategy = candidate,certificate,label
        break
    if data is None:
        return None,None,{**choices,"all_exact_origin_LDL_proposals_rejected":True}
    point,dual,tangent_choices = numerical.tangent_suggestion(data,matrix)
    trials = []
    for label,z,multipliers in (
        ("zero-tangent-zero-dual",[F(0)]*15,{"q":1,"terms":[]}),
        ("new-origin-tangent-zero-dual",point,{"q":1,"terms":[]}),
        ("new-origin-tangent-exact-dual",point,dual),
    ):
        support,_ = scalar.correlated_support({**data,"support_point":z},matrix,multipliers)
        trials.append((support,label,z,multipliers))
    _,label,point,dual = max(trials,key=lambda row:row[0])
    selected = {**selected,"quadratic_support_point":list(map(str,point)),"difference_dual":dual}
    result = bound(kernel,matrix,lower,upper,selected,radius,arcs)
    return selected,result,{
        **choices,**tangent_choices,"selected_exact_origin_diagonal_strategy":strategy,
        "selected_exact_origin_support_strategy":label,
        "only_exact_whole_branch_bound_decides_strictness":True,
    }
