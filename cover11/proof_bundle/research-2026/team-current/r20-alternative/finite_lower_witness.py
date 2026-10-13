# -*- coding: utf-8 -*-
"""
r20-alternative / finite TWO-DISK LOWER WITNESS for the n=11 residual hole (exact rationals).

Lead instruction (team-message-fefd66be): no line-direction grids, no "min over splits" global claims;
produce either a genuine finite LOWER WITNESS (P subset K, <=20 pts, no two radius-t disks cover P
=> rho2(K) > t) or an HONEST INSUFFICIENT WITNESS (surviving colouring with its explicit disks and a
K-point they violate).

Kernel structure reused from solo-20260922/verify_auxiliary_hole_lower.py:
  pair-forbidden: |p_i-p_j| > 2t ;  triple-forbidden: valid non-fitting certificate for a 3-point set.
Here the triple test is STRENGTHENED (still exact, still valid): a triple is forbidden if either
   (a) C462 variance test  V > t^2  (weights = circumcentre barycentrics, all >= 0), or
   (b) the circumcentre lies inside the triangle and R_circ > t   (then MEC = circumcircle > t).
Both are sound one-sided non-fitting certificates; using a SUBSET of valid constraints only makes
the UNSAT search conservative (if all colourings die, they die with the full constraint set too).

Caliber: ring centres = the 9 certified ring centres, radius fixed at R_D; membership is checked
STRICTLY at the rational upper radius R_up > R_D so every point is strictly inside U (no closure gap).
Hub test radius t = R_down - 1e-7, with R_down < R_D.  R_down = 0.3799838531, R_up = 0.3799838532.
"""
import json, time
import numpy as np
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
START = time.time()
R_down = F(3799838531, 10 ** 10)
R_up = F(3799838532, 10 ** 10)
T = F(3799837531, 10 ** 10)
print("t = %s = %.10f   (R_down = %.10f < R_D < R_up = %.10f)" % (T, T, R_down, R_up))

src = json.loads((ROOT / "n11" / "upper" / "certified_object.json").read_text(encoding="utf-8-sig"))
A = [tuple(F(int(x), 10 ** 17) for x in p) for i, p in enumerate(src["centers_scaled_1e17"]) if i not in (0, 2)]
dot = lambda a, b: sum(x * y for x, y in zip(a, b))
sub = lambda a, b: tuple(x - y for x, y in zip(a, b))
sq = lambda a, b: dot(sub(a, b), sub(a, b))


def strict_hole_ok(p):
    return sq(p, (0, 0)) < 1 and all(sq(p, a) > R_up * R_up for a in A)


def circumcentre(a, b, c):
    """exact circumcentre (Fractions) and barycentric weights wrt (a,b,c)."""
    u, v = sub(b, a), sub(c, a)
    uu, uv, vv = dot(u, u), dot(u, v), dot(v, v)
    det = uu * vv - uv * uv
    if det == 0:
        return None, None
    # solve  (O-a).u = uu/2 , (O-a).v = vv/2  for  O-a = alpha u + beta v
    alpha = (uu * vv - uv * vv) / (2 * det)          # vv(uu-uv)/(2 det)
    beta = (uu * vv - uv * uu) / (2 * det)           # uu(vv-uv)/(2 det)
    O = tuple(a[k] + alpha * u[k] + beta * v[k] for k in (0, 1))
    ws = [1 - alpha - beta, alpha, beta]
    return O, ws


def forbidden_sets(P, t):
    n = len(P)
    bad, certs = [], []
    for i, k in combinations(range(n), 2):
        m = sq(P[i], P[k]) - 4 * t * t
        if m > 0:
            bad.append((1 << i) | (1 << k))
            certs.append({"kind": "pair", "idx": [i, k], "margin": str(m)})
    for ids in combinations(range(n), 3):
        mask = sum(1 << i for i in ids)
        if any(mask & b == b for b in bad):
            continue
        a, b, c = [P[i] for i in ids]
        O, ws = circumcentre(a, b, c)
        if O is None:
            continue
        u, v = sub(b, a), sub(c, a)
        uu, uv, vv = dot(u, u), dot(u, v), dot(v, v)
        det = uu * vv - uv * uv
        mu = tuple(sum(w * P[i][k] for w, i in zip(ws, ids)) for k in (0, 1))
        V = sum(w * sq(P[i], mu) for w, i in zip(ws, ids))
        Rc2 = sq(O, a)
        if min(ws) >= 0 and V > t * t:
            bad.append(mask)
            certs.append({"kind": "triple-variance", "idx": list(ids), "margin": str(V - t * t)})
        elif min(ws) >= 0 and Rc2 > t * t:
            bad.append(mask)
            certs.append({"kind": "triple-circumcircle", "idx": list(ids), "margin": str(Rc2 - t * t)})
    return bad, certs


def search(P, t, cap=200):
    n = len(P)
    bad, certs = forbidden_sets(P, t)
    full = (1 << n) - 1
    surv, checked = [], 0
    for mask in range(1 << (n - 1)):
        checked += 1
        if not any(mask & b == b or (full ^ mask) & b == b for b in bad):
            surv.append(mask)
            if len(surv) > cap:
                break
    return bad, certs, surv, checked


def mec_exact(S):
    """exact MEC (radius^2, centre) for a small set of rational points, from 2- and 3-point candidates."""
    best = (None, None)
    if len(S) <= 1:
        return F(0), (S[0] if S else (F(0), F(0)))
    for a, b in combinations(S, 2):
        R2 = sq(a, b) / 4
        O = tuple((a[k] + b[k]) / 2 for k in (0, 1))
        if all(sq(p, O) <= R2 for p in S) and (best[0] is None or R2 < best[0]):
            best = (R2, O)
    for a, b, c in combinations(S, 3):
        O, ws = circumcentre(a, b, c)
        if O is None:
            continue
        R2 = sq(O, a)
        if all(sq(p, O) <= R2 for p in S) and (best[0] is None or R2 < best[0]):
            best = (R2, O)
    return best


core = json.loads((ROOT / "research-2026" / "solo-20260922" / "auxiliary_hole_core.json").read_text())
P = [tuple(map(F, p)) for p in core["points"]]
assert all(strict_hole_ok(p) for p in P)
Afloat = np.array([[float(x), float(y)] for x, y in A])
Rf = float(R_up)
Tf = float(T)
Cf = np.array([[float(c[0]), float(c[1])] for c in A])


def _rr_vertices(tol=1e-9):
    out = []
    for i, j in combinations(range(len(Cf)), 2):
        d = np.linalg.norm(Cf[j] - Cf[i])
        if d > 2 * Rf or d == 0:
            continue
        m = 0.5 * (Cf[i] + Cf[j]); u = (Cf[j] - Cf[i]) / d
        h = np.sqrt(max(0.0, Rf * Rf - d * d / 4)); w = np.array([-u[1], u[0]])
        for p in (m + h * w, m - h * w):
            if np.linalg.norm(p) >= 1:
                continue
            dm = np.linalg.norm(Cf - p, axis=1)
            if dm.min() < Rf - 1e-9:
                continue
            if int(np.sum(dm <= Rf + 1e-6)) <= 2:          # <=2 active => in K (perpendicular escape)
                out.append(p)
    return np.array(out) if out else np.zeros((0, 2))


def _line_vertices(n, t):
    out = []
    for c in Cf:
        z = t - n @ c
        if abs(z) > Rf:
            continue
        m = c + z * n
        h = np.sqrt(max(0.0, Rf * Rf - z * z)); w = np.array([-n[1], n[0]])
        for s in (-1, 1):
            p = m + s * h * w
            if np.linalg.norm(p) >= 1:
                continue
            dm = np.linalg.norm(Cf - p, axis=1)
            if dm.min() < Rf - 1e-9:
                continue
            if int(np.sum(dm <= Rf + 1e-6)) <= 2:
                out.append(p)
    return np.array(out) if out else np.zeros((0, 2))


def _ratio(p):
    q = (F(int(round(p[0] * 10 ** 12))), F(int(round(p[1] * 10 ** 12))), F(10 ** 12))
    return (q[0] / q[2], q[1] / q[2])


def _exact_closure_ok(p):
    """exact: |p|<1, every ring distance^2 >= R_down^2, and <=2 active rings (sufficient via perpendicular escape)."""
    if sq(p, (0, 0)) >= 1:
        return False
    if any(sq(p, a) < R_down * R_down for a in A):
        return False
    act = sum(1 for a in A if sq(p, a) <= R_up * R_up)
    return act <= 2


def find_violator(O0, O1):
    """R21/C456 vertex reduction: max over K of min(|x-O0|,|x-O1|) is attained on the split vertices."""
    o0 = np.array([float(O0[0]), float(O0[1])]); o1 = np.array([float(O1[0]), float(O1[1])])
    n = (o1 - o0) / np.linalg.norm(o1 - o0)
    t = (o1 @ o1 - o0 @ o0) / (2 * np.linalg.norm(o1 - o0))
    V = np.vstack([_rr_vertices(), _line_vertices(n, t)])
    if len(V) == 0:
        return None
    val = np.minimum(np.linalg.norm(V - o0, axis=1), np.linalg.norm(V - o1, axis=1))
    for j in np.argsort(-val)[:25]:
        cand = _ratio(V[j])
        if not _exact_closure_ok(cand):
            continue
        if min(sq(cand, O0), sq(cand, O1)) > T * T:
            return cand, float(val[j])
    return None


# ---------------- iteration: strengthen the point set until UNSAT or budget exhausted ----------------
for rnd in range(4):
    bad, certs, surv, checked = search(P, T, cap=400)
    print("\n[round %d] n=%d  forbidden=%d  checked=%d  survivors=%d"
          % (rnd, len(P), len(certs), checked, len(surv)))
    if not surv:
        print("\n*** LOWER WITNESS (exact, %d points) ***: no two disks of radius t cover P subset K" % len(P))
        print("    t = %s = %.12f  =>  rho2(K) > t ; upper bound (current hubs) rho2(K) <= R_D" % (T, T))
        (HERE / "finite_lower_witness.json").write_text(json.dumps(
            {"status": "LOWER WITNESS", "points": len(P), "hub_test_radius": str(T),
             "ring_radius_bounds": [str(R_down), str(R_up)], "n_forbidden": len(certs),
             "colourings_checked": checked, "forbidden_sets": certs,
             "point_set": [[str(x), str(y)] for x, y in P]}, indent=1), encoding="utf-8")
        print("    written finite_lower_witness.json ; elapsed %.1f s" % (time.time() - START))
        raise SystemExit(0)
    # evaluate survivors: which are realisable (both class MECs <= t)?
    rows = []
    for mask in surv:
        C1 = [P[i] for i in range(len(P)) if (mask >> i) & 1]
        C0 = [P[i] for i in range(len(P)) if not (mask >> i) & 1]
        r1, O1 = mec_exact(C1); r0, O0 = mec_exact(C0)
        rows.append((max(r1, r0), mask, C0, C1, r0, O0, r1, O1))
    rows.sort(key=lambda z: z[0])
    r_best, mask, C0, C1, r0, O0, r1, O1 = rows[0]
    print("    best survivor mask=%d  MEC0=%.12f  MEC1=%.12f  (t=%.12f)" % (mask, float(r0) ** .5, float(r1) ** .5, Tf))
    realisable = [z for z in rows if z[4] <= T * T and z[6] <= T * T]
    print("    realisable survivors (both classes fit radius t): %d" % len(realisable))
    if not realisable:
        print("    -> no realisable survivor: all survivors are excluded by their exact class MECs.")
        print("       (their MEC certificates are not in the forbidden list; report as insufficient witness)")
        break
    z = realisable[0]
    got = find_violator(z[5], z[7])
    if got is None:
        print("    -> no strict-hole point found beyond t from the survivor's own two centres:")
        print("       the %d-point set is 2-covered at radius t by those centres (INSUFFICIENT witness)." % len(P))
        break
    cand, val = got
    P.append(cand)
    print("    added violating strict-hole point (%.12f,%.12f), value %.12f > t" % (float(cand[0]), float(cand[1]), val))
    if len(P) > 20:
        print("    point budget (20) reached -> stop with INSUFFICIENT witness")
        break

(HERE / "finite_lower_witness.json").write_text(json.dumps(
    {"status": "INSUFFICIENT", "points": len(P), "hub_test_radius": str(T),
     "note": "finite set coverable or budget reached; not a lower witness",
     "point_set": [[str(x), str(y)] for x, y in P]}, indent=1), encoding="utf-8")
print("written finite_lower_witness.json (INSUFFICIENT) ; elapsed %.1f s" % (time.time() - START))
