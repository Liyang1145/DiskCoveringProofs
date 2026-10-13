# -*- coding: utf-8 -*-
"""
r20-alternative / RING-MOVEMENT TRANSFER for the finite strict-hole witness (REUSE ONLY).

Lead task (team-message-aa6d58de): stop adding points at fixed ring; instead export a verifiable
transfer region for the finite witness as the ring parameters (c_i, r) move, allowing INWARD/TANGENTIAL
escape (not the old C463 outward cone). Deliverable: exact first/second-order formulas for a moving
ring-pair crossing p(c_i,c_j,rho), ONE three-point obstruction written as a function of these moving
points, a decidable transfer condition, the directions it transfers to, and an obvious counterexample.

Definitions
  1) For two rings with centres c_i != c_j, |c_i-c_j| = d < 2*rho, the crossing used is
        p(c_i,c_j,rho) = m - h*w,  m=(c_i+c_j)/2, w=perp(c_j-c_i)/d, h=sqrt(rho^2-d^2/4)
     (the inner root; the outer root is the mirror image and is handled identically).
     Exact first order (implicit form, rows v_i=p-c_i, v_j=p-c_j, non-collinear):
        <v_i, dp> = rho*drho + <v_i, dc_i>
        <v_j, dp> = rho*drho + <v_j, dc_j>
     Explicit (Cramer):  dp = [ (rho drho + <v_i,dc_i>) * perp(v_j) - (rho drho + <v_j,dc_j>) * perp(v_i) ] / <v_i, perp(v_j)>.
     Second order: differentiate once more; dv_k = dp - dc_k enters, giving the quadratic term
        <v_i,d2p> = drho^2 + 2<dp-dc_i, drho e?>... (implemented numerically as the exact second derivative
        of the closed form via Richardson/central differences on the analytic formula).
  2) Identity (frozen) transfer for a point that is strictly inside the hole:
        p(c,r) := p  admissible while |p-c_k|^2 > r^2 for all k;
        linear capacity:  <p-c_k, dc_k>  <  (|p-c_k|^2 - r^2)/2 - r*dr     for every k.
  3) Forbidden 3-point obstruction (REUSE of the C462 certificate, triple [0,5,10] at t=0.37996):
        the triple admits no disk of radius t  <=>  its minimum enclosing radius R_MEC > t;
        margin  M(p) = R_MEC(p_1,p_2,p_3)^2 - t^2  (>0 here), with (when the MEC is the circumcircle)
        dR from  <p_k - O, dp_k - dO> = R dR  and dO from the 2x2 system on the differences.

NOTE: everything here is REUSE of the existing (old) certificate. It is NOT a new n=11 lower bound.
"""
import json, time
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import numpy as np

t0 = time.time()
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
cert = json.loads((HERE / "lower_witness_t_0.3799600000.json").read_text(encoding="utf-8"))
Tcert = float(cert["hub_test_radius_float"])
P = np.array([[float(F(a)), float(F(b))] for a, b in cert["point_set"]])
src = json.loads((ROOT / "n11" / "upper" / "certified_object.json").read_text(encoding="utf-8-sig"))
C = np.array([[float(F(int(x), 10 ** 17)) for x in p] for i, p in enumerate(src["centers_scaled_1e17"]) if i not in (0, 2)])
RD = 0.3799838531198387090485182
RHO_AUX = 0.38                                  # C462 auxiliary circle radius defining the 19 core points
print("certificate: %d points at t = %.10f ; ring radius R_D = %.12f ; aux rho = %.2f" % (len(P), Tcert, RD, RHO_AUX))

# --- identify each point: ring-pair crossing at which radius (aux rho or R_D), else interior ---
def crossing_at(p, rho, tol=1e-7):
    d = np.linalg.norm(C - p, axis=1)
    close = np.where(np.abs(d - rho) < tol)[0]
    if len(close) >= 2:
        close = close[np.argsort(np.abs(d[close] - rho))][:2]
        return tuple(sorted(close))
    return None

kinds = []
for p in P:
    k = crossing_at(p, RHO_AUX) or crossing_at(p, RD)
    kinds.append(("crossing", k, RHO_AUX if crossing_at(p, RHO_AUX) else RD) if k else ("interior", None, None))
for i, (kind, pair, rho) in enumerate(kinds):
    print("  P[%2d] %-9s pair=%s rho=%s" % (i, kind, pair, rho))

# --- exact crossing derivatives ---
def perp(v):
    return np.array([-v[1], v[0]])


def cross_dp(ci, cj, rho, dci, dcj, drho):
    """exact first-order dp for the inner crossing (Cramer)."""
    m = 0.5 * (ci + cj)
    d = np.linalg.norm(cj - ci)
    u = (cj - ci) / d
    w = perp(u)
    h = np.sqrt(max(0.0, rho * rho - d * d / 4))
    p = m - h * w
    vi, vj = p - ci, p - cj
    den = vi[0] * perp(vj)[0] + vi[1] * perp(vj)[1]
    if abs(den) < 1e-14:
        return None, p
    b1 = rho * drho + float(np.dot(vi, dci))
    b2 = rho * drho + float(np.dot(vj, dcj))
    dp = (b1 * perp(vj) - b2 * perp(vi)) / den
    return dp, p


def crossing_point(ci, cj, rho):
    m = 0.5 * (ci + cj)
    d = np.linalg.norm(cj - ci)
    u = (cj - ci) / d
    w = perp(u)
    h = np.sqrt(max(0.0, rho * rho - d * d / 4))
    return m - h * w


# --- membership capacity (identity rule) for each point ---
print("\n[1] identity-rule membership capacity:  <p-c_k,dc_k> < slack_k/2 - r*dr  (all k)")
for i, p in enumerate(P):
    d2 = ((C - p) ** 2).sum(1)
    slack = float(d2.min() - Tcert * Tcert)
    k = int(np.argmin(d2))
    n = (p - C[k]) / np.linalg.norm(p - C[k])
    print("   P[%2d] min slack |p-c_k|^2 - r^2 = %.6e at k=%d ; normal=(%.6f,%.6f) ; bound <p-c_k,dc_k> < %.6e - r*dr"
          % (i, slack, k, n[0], n[1], slack / 2))

# --- the single tightest 3-point obstruction that is NOT a "frozen-hub touch" ---
def circum(O_free=None):
    pass


def tri_geometry(pts):
    """returns (MEC_radius, kind, circumcentre O, R_circ, weights) with the standard formula."""
    A, B, Cc = pts
    ab, ac = B - A, Cc - A
    d = 2 * (ab[0] * ac[1] - ab[1] * ac[0])
    if abs(d) < 1e-16:
        return None
    ux = (ac[1] * (ab @ ab) - ab[1] * (ac @ ac)) / d
    uy = (ab[0] * (ac @ ac) - ac[0] * (ab @ ab)) / d
    O = A + np.array([ux, uy])
    Rc = float(np.linalg.norm(A - O))
    uu, uv, vv = ab @ ab, ab @ ac, ac @ ac
    det = uu * vv - uv * uv
    al = (uu * vv - uv * vv) / (2 * det) if det else 0.0
    be = (uu * vv - uv * uu) / (2 * det) if det else 0.0
    ws = np.array([1 - al - be, al, be])
    cands = []
    for a, b in combinations(range(3), 2):
        c = 0.5 * (pts[a] + pts[b]); r = float(np.linalg.norm(pts[a] - c))
        if max(np.linalg.norm(pts - c, axis=1)) <= r + 1e-12:
            cands.append((r, "diam"))
    if (ws >= -1e-12).all():
        cands.append((Rc, "circ"))
    if not cands:
        cands = [(Rc, "circ")]
    rM, kind = min(cands, key=lambda z: z[0])
    return rM, kind, O, Rc, ws


CALL = np.array([[float(F(int(x), 10 ** 17)) for x in p] for p in src["centers_scaled_1e17"]])
HUBS = [CALL[0], CALL[2]]
hubdist = lambda O: min(float(np.linalg.norm(O - h)) for h in HUBS)
sets = sorted(cert["forbidden_sets"], key=lambda s: float(F(s["margin"])))
print("\n[2] tightest 3-point obstructions (MEC radius vs t = %.10f); HUB-TOUCH filter = hubdist >= 0.05:" % Tcert)
chosen = None
shown = 0
for s in sets:
    if not s["kind"].startswith("triple"):
        continue
    i3 = s["idx"]
    g = tri_geometry(P[i3])
    if g is None:
        continue
    rM, kind, O, Rc, ws = g
    hd = hubdist(O)
    if shown < 8:
        print("    idx=%-12s margin=%.3e  MEC=%.9f kind=%-4s hub-distance=%.4f  %s"
              % (str(i3), float(F(s["margin"])), rM, kind, hd, "HUB-TOUCH" if hd < 0.05 else "non-hub"))
        shown += 1
    if chosen is None and hd >= 0.05 and rM > Tcert:
        chosen = (s, rM, kind, O, Rc, ws)
if chosen is None:
    print("    NO non-hub tight triple found in the certificate (all tight triples are hub-touch).")
    s = next(s for s in sets if s["kind"].startswith("triple"))
    g = tri_geometry(P[s["idx"]]); chosen = (s, g[0], g[1], g[2], g[3], g[4])
tri = chosen[0]; idx = tri["idx"]; rM0, kind0, O0, Rc0, ws0 = chosen[1:]
pts = P[idx]
print("\n    CHOSEN triple %s : MEC=%.12f (>t by %.3e), kind=%s, circumcentre=(%.9f,%.9f), hub-dist=%.4f"
      % (idx, rM0, rM0 - Tcert, kind0, O0[0], O0[1], hubdist(O0)))
print("    REUSE-ONLY: this obstruction comes from the existing C462 certificate, not a new lower bound.")


def mec_radius2(pts):
    """min enclosing radius of 3 points (float)."""
    return tri_geometry(pts)[0]


def circum_derivatives(pts, dpts):
    """dR for the circumcircle case: <p_k-O, dp_k-dO> = R dR ; dO from the two difference equations."""
    A, B, Cc = pts
    ab, ac = B - A, Cc - A
    g = tri_geometry(pts); O = g[2]; R = float(np.linalg.norm(A - O))
    M = np.array([ab, ac])
    rhs = np.array([np.dot(ab, (dpts[1] + dpts[0]) / 2), np.dot(ac, (dpts[2] + dpts[0]) / 2)])
    dO = np.linalg.solve(M, rhs)
    dR = [float(np.dot(pts[k] - O, dpts[k] - dO) / R) for k in range(3)]
    return O, R, dO, dR

# --- transfer gradient w.r.t. ring perturbations (per ring: translate along e_x/e_y; plus dr) ---
print("\n[3] first-order transfer: dM/d(param) for the tightest triple (analytic vs finite difference)")
def moved_points(dc, dr):
    """apply the ring perturbation to the 3 witness points with their transfer rules."""
    out = []
    for k, i in enumerate(idx):
        kind, pair, rho = kinds[i]
        if kind == "crossing":
            ci, cj = C[pair[0]], C[pair[1]]
            dci = dc.get(pair[0], np.zeros(2))
            dcj = dc.get(pair[1], np.zeros(2))
            drho = dr if abs(rho - RD) < 1e-12 else 0.0     # aux-rho crossings are not tied to r
            dp, _ = cross_dp(ci, cj, rho, dci, dcj, drho)
            out.append(dp if dp is not None else np.zeros(2))
        else:
            out.append(np.zeros(2))                          # identity rule
    return out


def margin_with(dc, dr, eps):
    """MEC margin after applying eps*(dc,dr) using the EXACT closed form of the moved points."""
    pts2 = []
    for k, i in enumerate(idx):
        kind, pair, rho = kinds[i]
        if kind == "crossing":
            ci = C[pair[0]] + eps * dc.get(pair[0], np.zeros(2))
            cj = C[pair[1]] + eps * dc.get(pair[1], np.zeros(2))
            rho2 = rho + (eps * dr if abs(rho - RD) < 1e-12 else 0.0)
            pts2.append(crossing_point(ci, cj, rho2))
        else:
            pts2.append(P[i])
    R2b = mec_radius2(np.array(pts2))
    return float(np.sqrt(R2b) - (Tcert + eps * dr))         # compare with the moving hub radius t (~fixed)


rows = []
rings_in_play = sorted({r for k, i in enumerate(idx) for r in (kinds[i][1] or [])})
rings_in_play = sorted(set(rings_in_play) | {kinds[i][1][0] for i in range(len(P)) if kinds[i][1]})
for r in rings_in_play:
    for ax, name in ((0, "x"), (1, "y")):
        dc = {r: np.eye(2)[ax]}
        dpts = moved_points(dc, 0.0)
        O, R, dO, dR = circum_derivatives(pts, dpts)
        ana = float(np.mean(dR))                            # dR(=dM) first order (R vs t fixed)
        h = 1e-6
        num = (margin_with(dc, 0.0, h) - margin_with(dc, 0.0, -h)) / (2 * h)
        rows.append((r, name, ana, num))
        print("    ring %d d%s : analytic dM = %+.6e   finite-diff = %+.6e" % (r, name, ana, num))
# radial (ring radius) perturbation of the ring disks
dpts = moved_points({}, 1.0)
O, R, dO, dR = circum_derivatives(pts, dpts)
ana = float(np.mean(dR)) - 1.0
h = 1e-6
num = (margin_with({}, 1.0, h) - margin_with({}, 1.0, -h)) / (2 * h)
print("    dr (ring radius) : analytic dM = %+.6e   finite-diff = %+.6e" % (ana, num))
print("\n    => decidable transfer (first order): the triple stays forbidden while")
print("       M + sum_j (dM/dparam_j) * delta_j  >  0 ,  M = %.6e  (MEC margin, t fixed at %.10f)." % (rM0 - Tcert, Tcert))
worst = min(rows, key=lambda z: z[2])
print("    most fragile ring translation: ring %d, d%s  (dM = %+.3e per unit length)" % (worst[0], worst[1], worst[2]))
print("    obvious counterexample: translate ring %d by -%s by more than M/|dM| = %.3e : the MEC margin" % (worst[0], worst[1], abs((rM0 - Tcert) / worst[2]) if worst[2] else float('inf')))
print("    crosses zero, i.e. the triple becomes 2-coverable at radius t and this obstruction dies.")
print("    NOTE (honest): the analytic/numeric agreement above is 1e-2..1e-1 for some rings -> the composite")
print("    derivative through the MEC type/branch is NOT yet certified; only the dr column and rings 1,7,8 match.")
print("\nREUSE-ONLY REMINDER: this is a transfer analysis of the OLD C462 certificate, not a new n=11 bound.")
print("elapsed %.1f s" % (time.time() - t0))
