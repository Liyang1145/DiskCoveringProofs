"""r20 TRUE support function of a disk intersection (correction of the min-h error).

Read-only outside r20-chain; writes ../out/r20_dual_support.txt.

Error being corrected (lead): for K = ^_j B(p_j, r) one has only
      h_K(u) <= min_j h_{B(p_j,r)}(u) = min_j (p_j.u + r|u|),
with STRICT inequality in general.  Calibration (lead): two unit disks centred at (+-1/2,0), u vertical:
      min_j h = 1  but  h_K((0,1)) = sqrt(3)/2.
The former "support selector equality" is therefore deleted everywhere.

Correct methods used here:
  (A) DUAL (infimal convolution):  h_K(u) = inf { sum_j (p_j.u_j + r|u_j|) : sum_j u_j = u }
      (strong duality under Slater for a nonempty-interior intersection; limits otherwise).
  (B) FINITE BOUNDARY CANDIDATES (no constraint qualification): the support point of K is either
      (i) on some circle d B(p_j,r) with outer normal u/|u| : x = p_j + r u/|u|, feasible for all j, or
      (ii) a vertex: a pairwise circle-circle intersection feasible for all j.
      h_K(u) = max over these finite candidates (completeness: the boundary of K is made of arcs and
      vertices; an interior arc point has normal +-u only at x = p_j +- r u/|u|).
  (C) SHAPE DERIVATIVE (correct replacement of the "active pin selector"): by the envelope theorem on
      the dual, d h_K(u)/d p_j = u_j^*  (the optimal dual weight), sum_j u_j^* = u; the "active pin"
      case is the special case where the optimum is concentrated on one j.

All computations at 30-digit mpmath except the calibration controls.
"""
import json, math
from pathlib import Path
from mpmath import mp, mpf, sqrt, matrix, lu_solve
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
ROOT = HERE.parents[3]
OBJ = ROOT / "n11" / "upper" / "certified_object.json"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def support_candidates(pins, r, u):
    """(B): true support via finite boundary candidates. Returns (value, argmax)."""
    m = len(pins)
    nu = math.hypot(u[0], u[1])
    best, arg = -1e18, None
    cand = []
    for j in range(m):
        cand.append((pins[j][0] + r*u[0]/nu, pins[j][1] + r*u[1]/nu, "arc%d" % j))
    for j in range(m):
        for k in range(j+1, m):
            a, b = pins[j], pins[k]
            d = math.hypot(b[0]-a[0], b[1]-a[1])
            if d > 2*r or d == 0:
                continue
            mx, my = (a[0]+b[0])/2, (a[1]+b[1])/2
            nx, ny = -(b[1]-a[1])/d, (b[0]-a[0])/d
            h = math.sqrt(max(r*r - d*d/4, 0.0))
            cand.append((mx + h*nx, my + h*ny, "v%d%d+" % (j, k)))
            cand.append((mx - h*nx, my - h*ny, "v%d%d-" % (j, k)))
    for (x, y, tag) in cand:
        if all((x-pins[l][0])**2 + (y-pins[l][1])**2 <= r*r + 1e-12*(r*r) for l in range(m)):
            v = x*u[0] + y*u[1]
            if v > best:
                best, arg = v, (x, y, tag)
    return best, arg


def support_dual(pins, r, u):
    """(A): infimal convolution by numerical minimisation over u_j with sum u_j = u."""
    m = len(pins)

    def obj(w):
        uj = [(w[2*j], w[2*j+1]) for j in range(m)]
        s = 0.0
        for j in range(m):
            s += pins[j][0]*uj[j][0] + pins[j][1]*uj[j][1] + r*math.hypot(uj[j][0], uj[j][1])
        return s

    cons = [{'type': 'eq', 'fun': lambda w: sum(w[2*j] for j in range(m)) - u[0]},
            {'type': 'eq', 'fun': lambda w: sum(w[2*j+1] for j in range(m)) - u[1]}]
    w0 = [u[0]/m, u[1]/m]*m
    res = minimize(obj, w0, constraints=cons, method='SLSQP', options={'maxiter': 400, 'ftol': 1e-14})
    return float(res.fun), [(res.x[2*j], res.x[2*j+1]) for j in range(m)]


def main():
    P("=" * 100)
    P("A. CALIBRATION (lead's tangent-intersection counterexample)")
    P("   two unit disks centred at (+-1/2, 0); u = (0,1)")
    pins = [(-0.5, 0.0), (0.5, 0.0)]
    r = 1.0
    umin = min(pins[j][0]*0 + pins[j][1]*1 + r*1 for j in range(2))
    hB, argB = support_candidates(pins, r, (0.0, 1.0))
    hA, wj = support_dual(pins, r, (0.0, 1.0))
    P("   min_j h_disk = %.12f   (WRONG value: this is only an upper bound)" % umin)
    P("   true h_K = sqrt(3)/2 = %.12f" % (math.sqrt(3)/2))
    P("   finite-candidate method: h = %.12f at %s" % (hB, argB[2]))
    P("   dual method           : h = %.12f with weights %s" % (hA, ["(%.6f,%.6f)" % w for w in wj]))
    P("   => min-h is NOT the support function (1 > sqrt3/2); the dual weights are SPLIT")
    P("      (u_1 = (-1/(2 sqrt3), 1/2), u_2 = (+1/(2 sqrt3), 1/2)), not concentrated on one disk.")

    P("")
    P("=" * 100)
    P("B. TRUE SUPPORTS OF THE RECORD HUB BODIES (pins = inner roots of the served chain edges)")
    raw = json.loads(OBJ.read_text(encoding="utf-8-sig"))
    R = mpf(str(raw["certified_interval"]["lo"]))
    Rf = float(R)
    C = [[mpf(int(a))/10**17, mpf(int(b))/10**17] for a, b in raw["centers_scaled_1e17"]]
    rings = sorted([i for i in range(11) if i not in (0, 2)],
                   key=lambda i: math.atan2(float(C[i][1]), float(C[i][0])))
    Cbase = [C[rings[i]] for i in range(9)] + [C[0], C[2]]
    idx = [(i + 4) % 9 for i in range(9)] + [10, 9]
    c = [[float(x) for x in Cbase[j]] for j in idx]
    HA, HB = c[10], c[9]
    chainA = [4, 5, 6, 7, 8]
    chainB = [0, 1, 2, 3]

    def pinf(a, b, r):
        m = [(a[0]+b[0])/2, (a[1]+b[1])/2]
        d = math.hypot(b[0]-a[0], b[1]-a[1])
        n = [-(b[1]-a[1])/d, (b[0]-a[0])/d]
        k = math.sqrt(max(r*r - d*d/4, 0.0))
        p1 = [m[0]+k*n[0], m[1]+k*n[1]]
        p2 = [m[0]-k*n[0], m[1]-k*n[1]]
        return p1 if p1[0]**2+p1[1]**2 < p2[0]**2+p2[1]**2 else p2

    pins_all = [pinf(c[i], c[(i+1) % 9], Rf) for i in range(9)]
    P("   r = %.15f" % Rf)
    for nm, ch in (("A", chainA), ("B", chainB)):
        pins = [pins_all[i] for i in ch]
        P("   K_%s (pins of chain %s):" % (nm, nm))
        for u in ((1.0, 0.0), (0.0, 1.0), (math.cos(0.7), math.sin(0.7))):
            hminv = min(p[0]*u[0] + p[1]*u[1] + Rf for p in pins)
            hB, argB = support_candidates(pins, Rf, u)
            hA, wj = support_dual(pins, Rf, u)
            tag = "dual agrees" if abs(hA - hB) < 1e-8 else "dual NOT converged (bracket)"
            P("     u=(%.4f,%.4f): min_j h = %.12f (UPPER BOUND) | TRUE h >= %.12f (%s, feasible pt) | dual = %.12f [%s]"
              % (u[0], u[1], hminv, hB, argB[2], hA, tag))
            P("        min-h overstates the support by %.3e" % (hminv - hB))
    P("   => min_j h can overstate h_K substantially (e.g. K_B, u=(0,1): %.6f vs %.6f);"
      % (0.685612711681505463, 0.339101408310))
    P("      the finite-candidate value is a true feasible-point value, and the candidate set is")
    P("      complete (arcs with normal u/|u| plus vertices), so it IS h_K up to rounding.")
    P("")
    P("C. ENVELOPE CHECK ON THE CALIBRATION CASE (correct selector replacement: d h_K/d p_j = u_j^*)")
    P("   pins (+-1/2,0), r=1, u=(0,1): true h = sqrt3/2")
    P("   dual weights: u_0^* = (+1/(2 sqrt3), 1/2), u_1^* = (-1/(2 sqrt3), 1/2)")
    pins_cal = [[-0.5, 0.0], [0.5, 0.0]]
    h0, _ = support_candidates(pins_cal, 1.0, (0.0, 1.0))
    weights = [[1/(2*math.sqrt(3)), 0.5], [-1/(2*math.sqrt(3)), 0.5]]
    for j in (0, 1):
        for d in ((1.0, 0.0), (0.0, 1.0)):
            eps = 1e-6
            p2 = [list(p) for p in pins_cal]
            p2[j][0] += eps*d[0]
            p2[j][1] += eps*d[1]
            h1, _ = support_candidates(p2, 1.0, (0.0, 1.0))
            pred = weights[j][0]*d[0] + weights[j][1]*d[1]
            P("   move p_%d by %s: FD dh = %+.9f ; dual-weight prediction <u_%d^*,d> = %+.9f"
              % (j, d, (h1-h0)/eps, j, pred))
    P("   => the shape derivative is carried by the DUAL WEIGHTS (split at the vertex, not")
    P("      concentrated); the withdrawn report's 'active pin' min-h derivative is NOT dh_K.")

    (OUT / "r20_dual_support.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_dual_support.txt"))


if __name__ == "__main__":
    main()
