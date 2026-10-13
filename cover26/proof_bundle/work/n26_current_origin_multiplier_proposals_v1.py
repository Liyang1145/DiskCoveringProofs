"""Current-domain NEW positive origin multipliers; ranking is never a proof."""

from fractions import Fraction as F

import numpy as np

import n26_full134rod_two_origin_kernel as origin
import n26_origin_branch_correlated_energy as energy


def scope(original):
    upper = F(234701,1000000)
    if not 0 < original["radius"] <= upper or 1-4*upper <= 0:
        raise ValueError("current origin condition lost its exact original radius screen")
    if origin.eligible_centers(original["data"][3]) != [16,25]:
        raise ValueError("current origin proposals changed the complete source owner bijection")


def prepare(bases):
    result = []
    for index,base in enumerate(bases):
        denominator = base["inverse_denominator"]
        result.append({
            "base":index,
            "left":np.array([i for i,j,w in base["pairs"]]),
            "right":np.array([j for i,j,w in base["pairs"]]),
            "pair_weights":np.array([float(F(w,base["energy_denominator"])) for i,j,w in base["pairs"]]),
            "W":F(sum(base["weights"]),base["scale"]),
            "owners":{
                owner:{
                    "harmonic":np.array([float(F(value,denominator)) for value in base["harmonic"][owner]]),
                    "R":F(base["scale"]*base["inverse"][owner][owner],denominator),
                } for owner in (16,25)
            },
        })
    return result


def rank(original,row,pending,bases):
    scope(original)
    broad = [i for i,(a,b) in enumerate(zip(row["sharp_lower"],row["sharp_upper"]))
             if F(b)-F(a) > F(1,10**7)]
    if len(broad) > 10:
        raise ValueError("origin numerical proposal ranking refuses an unbounded corner allocation")
    masks = np.arange(1<<len(broad))
    bits = np.array([((masks>>j)&1) for j in range(len(broad))]).T
    prepared,radius = prepare(bases),float(original["radius"])
    ranked = []
    for leaf in pending:
        lo,hi = np.array(list(map(float,map(F,leaf["lower"])))),np.array(list(map(float,map(F,leaf["upper"]))))
        points = np.tile((lo+hi)/2,(len(masks),1))
        points[:,broad] = lo[broad]+bits*(hi-lo)[broad]
        points = np.column_stack((np.zeros(len(points)+1),np.vstack((points,(lo+hi)/2))))
        cosines,sines = np.cos(2*np.pi*points),np.sin(2*np.pi*points)
        choices = {16:[],25:[]}
        for item in prepared:
            phi = 2*(1-np.cos(2*np.pi*(points[:,item["right"]]-points[:,item["left"]])))@item["pair_weights"]
            for owner in choices:
                data = item["owners"][owner]
                A = (cosines@data["harmonic"])**2+(sines@data["harmonic"])**2
                multipliers = {item["W"]*ratio for ratio in (F(1,1000),F(1,100),F(1,10),F(1),F(10))}
                # For a fixed point,margin gain is mu*A/(1+mu*R)-mu*rho^2.
                # Its stationary proposal is (sqrt(A)/rho-1)/R. This is only
                # numerical parameter selection,not a whole-domain optimum.
                for estimate in (float(min(A)),float(A[-1])):
                    raw = max(0.,(np.sqrt(max(0.,estimate))/radius-1)/float(data["R"]))
                    if np.isfinite(raw) and raw > 0:
                        multipliers.add(F(max(1,round(min(raw,1e60)*10**12)),10**12))
                for mu in sorted(multipliers):
                    if not 0 < mu <= 10**60:
                        continue
                    m,R,W = float(mu),float(data["R"]),float(item["W"])
                    scores = (phi+m/(1+m*R)*A)/(W+m)-radius*radius
                    choices[owner].append({
                        "origin_center_label":owner,"base_full_support_index":item["base"],
                        "origin_multiplier":str(mu),
                        "sampled_corner_score_NOT_a_lower_bound":float(min(scores)),
                    })
        for owner in choices:
            choices[owner].sort(key=lambda item:item["sampled_corner_score_NOT_a_lower_bound"],reverse=True)
            if not choices[owner]:
                raise ValueError("current origin numerical proposals omitted an entire actual owner")
        ranked.append({
            "actual_current_whole_leaf_index":leaf["index"],"owner_proposals":choices,
            "two_owner_sampled_score_NOT_a_lower_bound":min(
                choices[owner][0]["sampled_corner_score_NOT_a_lower_bound"] for owner in choices),
        })
    return sorted(ranked,key=lambda item:item["two_owner_sampled_score_NOT_a_lower_bound"],reverse=True)
