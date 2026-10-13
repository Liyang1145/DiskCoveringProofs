"""Numerical diagonal/tangent suggestions; ONLY exact existing gates decide.

Scales curvature correction cost by actual coordinate widths, rather than
using one correction on every broad angle. No source or proof cache imported.
"""

from fractions import Fraction as F

import numpy as np
from scipy.optimize import linprog, minimize

import n26_full134rod_correlated_quadratic_energy as exact
from n26_sharp_radius_constraints import SCALE


def correction_suggestion(minorant, lower, upper):
    widths = np.maximum(np.array([float(F(b)-F(a)) for a,b in zip(lower,upper)]),1e-14)
    H = np.array([[float(value) for value in row] for row in minorant])
    scaled = H*widths[:,None]*widths[None,:]
    unit = max(float(np.max(np.abs(scaled))),1e-30)
    B = scaled/unit
    margin = 1e-7
    initial = np.full(15,max(margin,-float(np.linalg.eigvalsh(B)[0])+margin))

    def eigenvalues(values):
        return np.linalg.eigvalsh(B+np.diag(values))-margin

    def jacobian(values):
        _,vectors = np.linalg.eigh(B+np.diag(values))
        return (vectors*vectors).T

    optimized = minimize(
        lambda values:float(np.sum(values)),initial,jac=lambda values:np.ones(15),
        method="SLSQP",bounds=[(0.,None)]*15,
        constraints={"type":"ineq","fun":eigenvalues,"jac":jacobian},
        options={"ftol":1e-11,"maxiter":240,"disp":False})
    candidates = []
    for label,values in (("width-balanced-SDP-suggestion",optimized.x),
                         ("width-scaled-isotropic-fallback",initial)):
        if not np.all(np.isfinite(values)):
            continue
        values = np.maximum(values,0)
        # The numerical safety pads are only suggestions; exact positive LDL
        # still rejects any insufficient correction after rational conversion.
        for pad in (1e-7,1e-5,1e-3):
            eta = (values+pad)*unit/(widths*widths)
            rational = [F(max(0,int(np.ceil(float(value)*10**20))),10**20) for value in eta]
            candidates.append((label+"-pad-"+str(pad),rational))
    return candidates,{
        "numerical_width_scaled_diagonal_optimization_success_NOT_proof":bool(optimized.success),
        "numerical_diagonal_iterations":int(optimized.nit),
        "numerical_width_scaled_eigenvalue_minimum_NOT_proof":float(min(eigenvalues(optimized.x))),
        "positive_LDL_still_required_for_every_rational_diagonal":True,
    }


def tangent_suggestion(data,matrix):
    a,b = np.array(list(map(float,data["lower_delta"]))),np.array(list(map(float,data["upper_delta"])))
    width = b-a
    Q = np.array([[float(value) for value in row] for row in data["quadratic"]])
    linear = np.array(list(map(float,data["linear"])))
    reference = data["reference"]
    pairs,rows,rhs = [],[],[]
    for i in range(16):
        for j in range(16):
            if i == j:
                continue
            row = np.zeros(15)
            if i:
                row[i-1] -= 1
            if j:
                row[j-1] += 1
            pairs.append((i,j))
            rows.append(row)
            rhs.append(float(F(matrix[i][j],SCALE)-reference[j]+reference[i]))
    rows,rhs = np.array(rows),np.array(rhs)
    scaled = rows*width
    right = rhs-rows@a
    scales = np.maximum(np.maximum(np.max(np.abs(scaled),axis=1),np.abs(right)),1e-14)
    scaled,right = scaled/scales[:,None],right/scales
    bounds = [(0.,0. if value == 0 else 1.) for value in width]
    start = np.full(15,.5)
    start[width == 0] = 0
    objective_scale = 10**8

    def value(point):
        delta = a+width*point
        return float((linear@delta+delta@Q@delta/2)*objective_scale)

    optimized = minimize(
        value,start,jac=lambda point:width*(linear+Q@(a+width*point))*objective_scale,
        method="SLSQP",bounds=bounds,
        constraints={"type":"ineq","fun":lambda point:right-scaled@point,
                     "jac":lambda point:-scaled},
        options={"ftol":1e-12,"maxiter":240,"disp":False})
    delta = a+width*optimized.x
    if not np.all(np.isfinite(delta)):
        delta = np.zeros(15)
    point = [F(round(float(value)*10**16),10**16) for value in delta]
    tangent = [linear+sum(row[j]*point[j] for j in range(15))
               for linear,row in zip(data["linear"],data["quadratic"])]
    lp = linprog(width*np.array(list(map(float,tangent)))*objective_scale,
                 A_ub=scaled,b_ub=right,bounds=bounds,method="highs")
    denominator,terms = 10**30,[]
    if lp.success:
        for (i,j),mu,scale in zip(pairs,lp.ineqlin.marginals,scales):
            numerator = max(0,round(-float(mu)*denominator/(objective_scale*float(scale))))
            if numerator:
                terms.append([i,j,str(numerator)])
    return point,{"q":denominator,"terms":terms},{
        "numerical_correlated_QP_success_NOT_proof":bool(optimized.success),
        "numerical_correlated_QP_iterations":int(optimized.nit),
        "numerical_linear_support_dual_success_NOT_proof":bool(lp.success),
    }


def suggest(kernel,matrix,lower,upper,reference,radius,arcs,parts=8):
    minorant = exact.full.combined_minorant(kernel,matrix,reference,lower,upper,arcs,parts)
    corrections,numerical = correction_suggestion(minorant,lower,upper)
    reference = list(map(str,reference))
    selected_data,certificate,strategy = None,None,None
    for label,correction in corrections:
        candidate = {
            "schema":exact.SCHEMA,"reference_turns":reference,"parts":parts,
            "curvature_correction":list(map(str,correction)),
            "quadratic_support_point":["0"]*15,"difference_dual":{"q":1,"terms":[]},
        }
        try:
            data = exact.quadratic_data(kernel,matrix,lower,upper,candidate,arcs)
        except ValueError:
            continue
        selected_data,certificate,strategy = data,candidate,label
        break
    if selected_data is None:
        return None,None,{**numerical,"all_rational_LDL_candidates_rejected":True}
    point,dual,tangent_numerical = tangent_suggestion(selected_data,matrix)
    candidates = []
    for label,z,multipliers in (
        ("zero-tangent-zero-dual",[F(0)]*15,{"q":1,"terms":[]}),
        ("fresh-tangent-zero-dual",point,{"q":1,"terms":[]}),
        ("fresh-tangent-exact-LP-dual",point,dual),
    ):
        support,_ = exact.correlated_support({**selected_data,"support_point":z},matrix,multipliers)
        candidates.append((support,label,z,multipliers))
    _,label,point,dual = max(candidates,key=lambda row:row[0])
    certificate = {**certificate,"quadratic_support_point":list(map(str,point)),"difference_dual":dual}
    result = exact.bound(kernel,matrix,lower,upper,certificate,radius,arcs)
    return certificate,result,{
        **numerical,**tangent_numerical,"selected_exact_positive_diagonal_strategy":strategy,
        "selected_exact_correlated_support_strategy":label,
        "whole_closed_leaf_strictness_decided_ONLY_by_existing_exact_bound":True,
    }
