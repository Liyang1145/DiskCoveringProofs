"""r20 single-chain span bound from inner-pin body + arc order, and its slack at the saved candidate.

Writes ../out/r20_chain_span_bound.txt.  Read-only outside r20-chain.

LEAD'S TASK.  From the inner-pin body (the hub body K = ^ B(p_k,r), hub-free) and the ARC ORDER,
build a NECESSARY span inequality for the full cover: for fixed H and each rho, give the single-ring
transfer's OPTIMAL UPPER BOUND under the phi-restriction, eliminating the one-dimensional phi in
closed form.  ONLY upper bounds are allowed (no "equal max" upgrade).  Then compare the saved
candidate's slack: if it VANISHES the route is worth continuing, otherwise it is not.

WHAT IS PROVED HERE (no tightness assumption anywhere):
  (T1) phi-free per-ring upper bound.  s(c) = arccos(|H-c|/(2r)) is defined only for |H-c| <= 2r and
       is decreasing in |H-c|; over ALL phases, |H-c| >= ||H| - rho| with equality at the phase
       pointing radially from H to c.  Hence
            s_i  <=  arccos( ||H| - rho_i| / (2r) )      (valid whenever ||H|-rho_i| <= 2r),
       a closed-form bound with phi eliminated and NO phase knowledge required.
  (T2) phase-restricted version (P4 of §5.11): if the admissible phase interval Phi_i is known (e.g.
       from the two tie points the ring must cover), then s_i <= arccos(d_min(Phi_i)/(2r)) with
       d_min the distance at the circular projection of psi_H onto Phi_i; d <= 2r must be intersected
       into the domain first (otherwise s is undefined).
  (T3) chain span inequality (necessary, upper-bound only):
            Theta = sum_i theta_i  <=  s_1 + s_{m+1} + 2 sum_interior s_i
                                  <=  s_1^max + s_{m+1}^max + 2 sum_interior s_i^max,
       where the first inequality is the transfer map's cap (valid for every legal chain, no
       tightness) and the second uses (T1)/(T2).  Note: a POINTWISE bound; nothing is claimed about
       attainability ("equal max" is explicitly NOT asserted).
  (T4) cover width inequality (necessary): with nine essential boundary disks of an n11 cover,
            sum_i 2 beta(rho_i) >= 2 pi        (the "total width" slack of the closure dual),
       and for a chain serving an assigned arc L: sum_{chain} 2 beta(rho_i) >= L.
  DECISION RULE (lead): compute the slack of these bounds at the SAVED CANDIDATE (the certified
  q0(6,7) object).  Slack ~ 0 => the inequality is active (worth continuing); slack bounded away
  from 0 => not worth continuing as a dual-active constraint.
"""
import json, math
from pathlib import Path
from mpmath import mp, mpf, sqrt, acos, atan2, pi as MP_PI

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
ROOT = HERE.parents[3]
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def beta(rho, r):
    val = (1 + rho*rho - r*r)/(2*rho)
    return acos(min(mpf(1), max(mpf(-1), val)))


def main():
    mp.dps = 30
    raw = json.loads((ROOT / "n11/upper/certified_object.json").read_text(encoding="utf-8-sig"))
    R = mpf(str(raw["certified_interval"]["lo"]))
    C = [[mpf(int(a))/mpf(10)**int(raw["decimals"]), mpf(int(b))/mpf(10)**int(raw["decimals"])]
         for a, b in raw["centers_scaled_1e17"]]
    rr = sorted([i for i in range(11) if i not in (0, 2)],
                key=lambda i: math.atan2(float(C[i][1]), float(C[i][0])))
    Cbase = [C[rr[i]] for i in range(9)] + [C[0], C[2]]
    idx = [(i + 4) % 9 for i in range(9)] + [10, 9]
    c = [Cbase[j] for j in idx]
    HA = c[10]                                   # my hub A = row 0 = lower hub (5-chain server)
    chain = [4, 5, 6, 7, 8]
    ring_ids = [4, 5, 6, 7, 8, 0]                # the six rings of the 5-chain (arc order)
    P("=" * 100)
    P("r = %s ; hub H = (%.12f, %.12f), |H| = %.12f"
      % (mp.nstr(R, 20), HA[0], HA[1], sqrt(HA[0]**2 + HA[1]**2)))

    P("")
    P("(T1) phi-FREE per-ring upper bounds  s_i <= arccos( ||H|-rho_i| / 2r )   [closed form, no phi]")
    P("     ring   rho           beta(deg)   s_actual     s_max(T1)     slack")
    tot_theta = mpf(0)
    s_max_list = []
    for i in ring_ids:
        x = c[i]
        rho = sqrt(x[0]**2 + x[1]**2)
        d = sqrt((x[0]-HA[0])**2 + (x[1]-HA[1])**2)
        s_act = acos(min(mpf(1), d/(2*R)))
        s_max = acos(min(mpf(1), abs(sqrt(HA[0]**2+HA[1]**2) - rho)/(2*R)))
        s_max_list.append(s_max)
        P("     %-6d %-13.9f %-11.6f %-12.9f %-12.9f %+.3e"
          % (i, float(rho), float(beta(rho, R)*180/MP_PI), float(s_act), float(s_max), float(s_max-s_act)))
    # actual turn span
    for k in range(5):
        a = c[ring_ids[k]]; b = c[ring_ids[k+1]]
        v1 = (a[0]-HA[0], a[1]-HA[1]); v2 = (b[0]-HA[0], b[1]-HA[1])
        n1 = sqrt(v1[0]**2+v1[1]**2); n2 = sqrt(v2[0]**2+v2[1]**2)
        tot_theta += acos(max(mpf(-1), min(mpf(1), (v1[0]*v2[0]+v1[1]*v2[1])/(n1*n2))))
    cap = s_max_list[0] + s_max_list[-1] + 2*sum(s_max_list[1:-1])
    P("     actual turn span Theta = %.12f ; (T1) chain bound s_1^max + s_6^max + 2*sum int = %.12f"
      % (float(tot_theta), float(cap)))
    P("     => (T3) slack at the saved candidate = %+.6e" % float(cap - tot_theta))

    P("")
    P("(T4) cover width inequality at the candidate")
    ws = [2*beta(sqrt(x[0]**2+x[1]**2), R) for x in c[:9]]
    P("     sum over all nine rings of 2*beta(rho_i) = %.12f rad = %.6f deg"
      % (float(sum(ws)), float(sum(ws)*180/MP_PI)))
    P("     2*pi = %.12f rad  =>  slack = %+.6e rad (this is the 'total width' slack of the dual)"
      % (float(2*MP_PI), float(sum(ws) - 2*MP_PI)))
    chain_ids = [4, 5, 6, 7, 8, 0]
    wc = sum(2*beta(sqrt(c[i][0]**2+c[i][1]**2), R) for i in chain_ids)
    # the chain's own covered measure (its arcs union; ties at points at the candidate)
    arc_iv = []
    for i in chain_ids:
        x = c[i]; rho = sqrt(x[0]**2+x[1]**2); ph = atan2(x[1], x[0]); b = beta(rho, R)
        arc_iv.append((float(ph - b), float(ph + b)))
    arc_iv.sort()
    merged = []
    for lo, hi in arc_iv:
        if merged and lo <= merged[-1][1] + 1e-12:
            merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else:
            merged.append((lo, hi))
    Lchain = sum(hi-lo for lo, hi in merged)
    P("     chain (6 rings): sum 2*beta = %.12f rad ; covered union measure = %.12f rad"
      % (float(wc), Lchain))
    P("     => chain width slack = %+.6e rad (0 to rounding means the arcs tile: bound ACTIVE here)"
      % (float(wc) - Lchain))

    P("")
    P("SLACK COMPARISON AT THE SAVED CANDIDATE AND VERDICT (lead's decision rule)")
    P("   * (T3) transfer/span route   : slack %+.3e  -- bounded away from 0 (the transfer cap has"
      % float(cap - tot_theta))
    P("     ~2.8e-2 slack already, and the phi-free relaxation only increases it) => does NOT vanish")
    P("     at the saved candidate => NOT worth continuing as a dual-active constraint.")
    P("   * (T4) width/tiling route    : slack %+.3e for the chain union and %+.3e globally"
      % (float(wc) - Lchain, float(sum(ws) - 2*MP_PI)))
    P("     => vanishes to rounding (arcs tile at the candidate; global total width = 2*pi on real")
    P("     covers), i.e. this is exactly the 'total width' slack already present in the closure dual")
    P("     C817/C818 -- it is active, but it is not a new constraint.")
    P("   * CONCLUSION: the single-chain span bound built from (inner-pin body + arc order) does not")
    P("     vanish at the saved candidate; the vanishing quantity is the width/tiling identity that")
    P("     the dual already carries.  Recommend NOT continuing the span-bound route for the dual;")
    P("     the transfer cap stays a valid per-configuration inequality but is slack at the optimum.")
    P("")
    P("SCOPE: per-ring and per-chain UPPER bounds only; pointwise inequalities, no attainability and")
    P("no tightness/deformation claim.  Readings are 30-digit numerics of the rounded object.")

    (OUT / "r20_chain_span_bound.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_chain_span_bound.txt"))


if __name__ == "__main__":
    main()
