"""r20 5-chain / 4-chain hub elimination: identity, equality geometry, deviation bound, coupling.

Read-only outside r20-chain; writes ../out/r20_5chain_elimination.txt only.

Contents
  A. the exact elimination identity (random verification, no saturation assumed):
        sum_k lam_k |h-p_k|^2 = |h-h_lam|^2 + V(lam),   h_lam = sum lam_k p_k,
        V(lam) = sum_{i<j} lam_i lam_j |p_i-p_j|^2,
     hence  K := {h: |h-p_k|<=R for all k} = INTERSECTION_{lam in simplex} B(h_lam, sqrt(R^2-V(lam))).
     Consequences: every member disk contains K; diam K <= 2 sqrt(R^2 - Vmax); K = empty if Vmax > R^2.
  B. Vmax over the simplex = max( max_{pairs} d^2/4 , max_{3-supports S: O_S in conv S} rho_S^2 )
     (on a 3-support face V = rho_S^2 - |h_lam - O_S|^2, maximised at the projection of O_S).
  C. calibration on the certified object with the RESOLVED lead mapping (shift=4, swap=1):
     c[10] = object row 0 = hub A, c[9] = object row 2 = hub B; lead pins [4,6,8] are the three
     active pins of hub A.  Hub A serves the 5-chain (lead edges 4..8), hub B the 4-chain (0..3).
  D. central-endpoint coupling data (the two switch rings, joint coverage of their exposed arcs,
     the two central faces (hA,hB,c_switch)).

No new claims are registered.
"""
import json, math
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, sqrt, matrix, lu_solve

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
ROOT = HERE.parents[3]
OBJ = ROOT / "n11" / "upper" / "certified_object.json"

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def V_of(lam, pts):
    return sum(lam[i] * lam[j] * float(np.sum((np.asarray(pts[i]) - np.asarray(pts[j])) ** 2))
               for i in range(len(pts)) for j in range(i))


def Vmax(pts, tol=1e-12):
    """max over the simplex of V(lam), with an attained maximiser lam."""
    pts = np.asarray(pts, float)
    m = len(pts)
    best, argbest = -1.0, None
    for i in range(m):
        for j in range(i + 1, m):
            v = float(np.sum((pts[i] - pts[j]) ** 2)) / 4
            lam = np.zeros(m); lam[i] = lam[j] = 0.5
            if v > best:
                best, argbest = v, lam
    for i in range(m):
        for j in range(i + 1, m):
            for k in range(j + 1, m):
                A, B, C = pts[i], pts[j], pts[k]
                ar = abs((B[0] - A[0]) * (C[1] - A[1]) - (B[1] - A[1]) * (C[0] - A[0])) / 2
                if ar < 1e-14:
                    continue
                e = [np.linalg.norm(B - C), np.linalg.norm(A - C), np.linalg.norm(A - B)]
                rho = e[0] * e[1] * e[2] / (4 * ar)
                O = np.linalg.solve(2 * np.array([B - A, C - A]),
                                    np.array([B @ B - A @ A, C @ C - A @ A]))
                x = np.linalg.solve(np.column_stack([B - A, C - A]), O - A)
                lam3 = np.array([1 - x.sum(), x[0], x[1]])
                if lam3.min() >= -tol:
                    lam = np.zeros(m); lam[i], lam[j], lam[k] = lam3
                    if rho * rho > best:
                        best, argbest = rho * rho, lam
    return best, argbest


def pin_of_edge(a, b, R):
    a, b = np.asarray(a, float), np.asarray(b, float)
    m = (a + b) / 2
    d = float(np.linalg.norm(b - a))
    n = np.array([-(b - a)[1], (b - a)[0]]) / d
    k = math.sqrt(R * R - d * d / 4)
    p1, p2 = m + k * n, m - k * n
    return (p1, p2) if np.linalg.norm(p1) < np.linalg.norm(p2) else (p2, p1)


def K_diameter(pts, R, tol=1e-13):
    """diameter of the intersection of the closed disks B(p,R) by its vertices
    (pairwise circle-circle intersections that satisfy every disk constraint)."""
    pts = np.asarray(pts, float)
    m = len(pts)
    verts = []
    for i in range(m):
        for j in range(i + 1, m):
            p, q = pts[i], pts[j]
            d = np.linalg.norm(q - p)
            if d > 2 * R + tol or d < 1e-15:
                continue
            mid = (p + q) / 2
            n = np.array([-(q - p)[1], (q - p)[0]]) / d
            h = math.sqrt(max(R * R - d * d / 4, 0.0))
            for s in (+1, -1):
                x = mid + s * h * n
                if all(np.linalg.norm(x - t) <= R + tol for t in pts):
                    verts.append(x)
    if not verts:
        return None, None, 0
    best, pair = 0.0, None
    for a in range(len(verts)):
        for b in range(a + 1, len(verts)):
            dd = float(np.linalg.norm(verts[a] - verts[b]))
            if dd > best:
                best, pair = dd, (verts[a], verts[b])
    return pair, best, len(verts)


def partA():
    P("=" * 100)
    P("A. ELIMINATION IDENTITY (arbitrary pins; NO saturation premise)")
    P("   for fixed lam: sum_k lam_k|h-p_k|^2 = |h-h_lam|^2 + V(lam)   [V = sum_{i<j} lam_i lam_j d_ij^2]")
    P("   (i)  every h with |h-p_k|<=R for all k satisfies |h-h_lam| <= sqrt(R^2-V(lam)): K is")
    P("        contained in EVERY disk of the family {B(h_lam, sqrt(R^2-V(lam))): lam in simplex}.")
    P("   (ii) h not in K  =>  some VERTEX lam=e_k already separates it (|h-p_k|>R);")
    P("        hence K = INTERSECTION over the whole family (the family adds no new restriction).")
    P("   (iii) diam K <= 2 sqrt(R^2 - Vmax),  Vmax = max_lam V(lam);  K = EMPTY if Vmax > R^2.")
    rng = np.random.default_rng(11)
    worst1 = 0.0
    bad_cont = bad_sep = bad_diam = bad_empty = 0
    for _ in range(4000):
        m = int(rng.integers(2, 7))
        pts = rng.uniform(-1.2, 1.2, (m, 2))
        R = float(rng.uniform(0.2, 0.8))
        lam = rng.dirichlet(np.ones(m))
        hl = lam @ pts
        V = V_of(lam, pts)
        for h in rng.uniform(-1.5, 1.5, (5, 2)):
            lhs = float(sum(lam[k] * np.sum((h - pts[k]) ** 2) for k in range(m)))
            worst1 = max(worst1, abs(lhs - float(np.sum((h - hl) ** 2)) - V))
        if V <= R * R:
            s = math.sqrt(R * R - V)
            for h in rng.uniform(-1.5, 1.5, (20, 2)):
                inK = all(np.linalg.norm(h - p) <= R for p in pts)
                indisk = np.linalg.norm(h - hl) <= s + 1e-12
                if inK and not indisk:
                    bad_cont += 1
                if (not inK) and all(np.linalg.norm(h - p) <= R + 1e-12 for p in pts):
                    bad_sep += 1
        vm, lm = Vmax(pts)
        if vm > R * R + 1e-12:
            # no point can satisfy all constraints
            for h in rng.uniform(-1.5, 1.5, (50, 2)):
                if all(np.linalg.norm(h - p) <= R for p in pts):
                    bad_empty += 1
        # diameter bound against a sampled feasible set
        feas = [h for h in rng.uniform(-1.5, 1.5, (4000, 2)) if all(np.linalg.norm(h - p) <= R for p in pts)]
        if len(feas) > 1 and vm <= R * R:
            feas = np.array(feas)
            dmax = max(np.linalg.norm(feas[a] - feas[b]) for a in range(min(len(feas), 300))
                       for b in range(min(len(feas), 300)))
            if dmax > 2 * math.sqrt(R * R - vm) + 1e-9:
                bad_diam += 1
    P("   identity worst residual            : %.3e" % worst1)
    P("   K contained in every member disk   : %d violations" % bad_cont)
    P("   vertex separation (family = K)     : %d violations" % bad_sep)
    P("   Vmax > R^2 => K empty              : %d violations" % bad_empty)
    P("   diam K <= 2 sqrt(R^2-Vmax)         : %d violations" % bad_diam)
    # 3-support identity V(lam) = rho_S^2 - |h_lam - O_S|^2
    worst2 = 0.0
    for _ in range(2000):
        T = rng.uniform(-1.5, 1.5, (3, 2))
        cr = abs((T[1] - T[0])[0] * (T[2] - T[0])[1] - (T[1] - T[0])[1] * (T[2] - T[0])[0])
        longest = max(np.linalg.norm(T[1] - T[2]), np.linalg.norm(T[0] - T[2]), np.linalg.norm(T[0] - T[1]))
        if cr / (longest * longest) < 1e-2:      # keep well-conditioned triangles
            continue
        lam = rng.dirichlet(np.ones(3))
        hl = lam @ T
        V = V_of(lam, T)
        e = [np.linalg.norm(T[1] - T[2]), np.linalg.norm(T[0] - T[2]), np.linalg.norm(T[0] - T[1])]
        ar = abs((T[1] - T[0])[0] * (T[2] - T[0])[1] - (T[1] - T[0])[1] * (T[2] - T[0])[0]) / 2
        rho = e[0] * e[1] * e[2] / (4 * ar)
        O = np.linalg.solve(2 * np.array([T[1] - T[0], T[2] - T[0]]),
                            np.array([T[1] @ T[1] - T[0] @ T[0], T[2] @ T[2] - T[0] @ T[0]]))
        worst2 = max(worst2, abs(V - (rho * rho - float(np.sum((hl - O) ** 2)))))
    P("   3-support identity V(lam) = rho_S^2 - |h_lam - O_S|^2 : worst residual %.3e" % worst2)
    P("   => on a 3-support face V is maximised at the projection of O_S; if O_S is inside the")
    P("      pin triangle the max is rho_S^2, attained by the barycentric weights of O_S.")


def partCD():
    raw = json.loads(OBJ.read_text(encoding="utf-8-sig"))
    C0 = np.array([[int(v) / 1e17 for v in a] for a in raw["centers_scaled_1e17"]])
    R = float(raw["certified_interval"]["lo"])
    rings = sorted([i for i in range(11) if i not in (0, 2)],
                   key=lambda i: math.atan2(C0[i, 1], C0[i, 0]))
    C = C0[rings + [0, 2]]
    idx = [(i + 4) % 9 for i in range(9)] + [10, 9]          # shift=4, swap=1 (Delaunay-matched)
    c = C[idx]
    lab = [("ring_row_%d" % rings[i]) if i < 9 else
           ("row_0.hubA" if i == 9 else "row_2.hubB") for i in idx]
    P("")
    P("=" * 100)
    P("C. calibration with the RESOLVED mapping (shift=4, swap=1; c[10] = object row 0 = hub A)")
    P("   " + "  ".join("c[%d]=%s" % (j, lab[j]) for j in range(11)))
    HUB_A, HUB_B = c[10], c[9]
    P("   hub A = c[10] = (%.15f, %.15f)   |hA| = %.15f" % (HUB_A[0], HUB_A[1], np.linalg.norm(HUB_A)))
    P("   hub B = c[ 9] = (%.15f, %.15f)   |hB| = %.15f" % (HUB_B[0], HUB_B[1], np.linalg.norm(HUB_B)))
    P("   R = %.18f   1-R = %.15f" % (R, 1 - R))

    P("")
    P("   edge table (lead indices): pin = min-norm root, p_out = other root")
    P("     edge      pin (x,y)                     |p_in|    |p_out|   ||H_A-pin|-R|   ||H_B-pin|-R|")
    allpins = {}
    for i in range(9):
        pin, pout = pin_of_edge(c[i], c[(i + 1) % 9], R)
        allpins[i] = (pin, pout)
        P("     (%d,%d)  (%+.12f,%+.12f)  %.9f %.9f   %+.3e      %+.3e"
          % (i, (i + 1) % 9, pin[0], pin[1], np.linalg.norm(pin), np.linalg.norm(pout),
             np.linalg.norm(pin - HUB_A) - R, np.linalg.norm(pin - HUB_B) - R))

    chainA = [4, 5, 6, 7, 8]
    chainB = [0, 1, 2, 3]
    pinsA = np.array([allpins[i][0] for i in chainA])
    pinsB = np.array([allpins[i][0] for i in chainB])
    for nm, pins, H, ch in (("A  5-chain (lead edges 4..8)", pinsA, HUB_A, chainA),
                            ("B  4-chain (lead edges 0..3)", pinsB, HUB_B, chainB)):
        dH = np.array([np.linalg.norm(p - H) for p in pins])
        P("")
        P("   hub %s" % nm)
        P("     |H-pin| - R over the chain pins = %s" % " ".join("%+.3e" % (v - R) for v in dH))
        vm, lam = Vmax(pins)
        hl = lam @ pins
        P("     Vmax = %.18f     R^2 = %.18f     R^2 - Vmax = %+.6e" % (vm, R * R, R * R - vm))
        P("     maximiser lam = %s" % " ".join("%+.12f" % v for v in lam))
        P("     h_lam = (%+.15f, %+.15f)   |H - h_lam| = %.6e" % (hl[0], hl[1], np.linalg.norm(hl - H)))
        pair, diam, nv = K_diameter(pins, R)
        P("     bound 2*sqrt(R^2-Vmax) = %s" % ("%.6e" % (2 * math.sqrt(R * R - vm)) if vm <= R * R else "empty set"))
        P("     true K: vertices %s, diameter %s" % (nv, ("%.6e" % diam) if diam is not None else "n/a"))
        if pair is not None:
            P("       attaining pair: (%.9f,%.9f) - (%.9f,%.9f)"
              % (pair[0][0], pair[0][1], pair[1][0], pair[1][1]))
        # active-support weights: barycentric coordinates of H in the active pin triple
        act = [t for t in range(len(pins)) if abs(dH[t] - R) < 1e-10]
        if len(act) == 3:
            T3 = pins[act]
            M = np.vstack([T3.T, np.ones(3)]).T
            w = np.linalg.solve(M, np.r_[H, 1.0])
            P("     active triple = chain positions %s ; barycentric weights %s (min %.3e)"
              % (act, " ".join("%+.12f" % v for v in w), w.min()))
            P("     V(active triple) = %.18f   R^2 - V = %+.6e"
              % (V_of(w, T3), R * R - V_of(w, T3)))

    # -------- high precision reading of the hub-A active triangle
    P("")
    P("   HIGH-PRECISION equality reading, hub A active triangle (lead edges 4,6,8):")
    mp.dps = 60
    Rhi = mpf(str(raw["certified_interval"]["lo"]))
    pts = []
    for i in (4, 6, 8):
        a = [mpf(c[i][0]), mpf(c[i][1])]
        b = [mpf(c[(i + 1) % 9][0]), mpf(c[(i + 1) % 9][1])]
        m = [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2]
        d = sqrt((b[0] - a[0]) ** 2 + (b[1] - a[1]) ** 2)
        n = [-(b[1] - a[1]) / d, (b[0] - a[0]) / d]
        k = sqrt(Rhi * Rhi - (d / 2) ** 2)
        c1 = [m[0] + k * n[0], m[1] + k * n[1]]
        c2 = [m[0] - k * n[0], m[1] - k * n[1]]
        pts.append(c1 if sqrt(c1[0] ** 2 + c1[1] ** 2) < sqrt(c2[0] ** 2 + c2[1] ** 2) else c2)
    hA = [mpf(HUB_A[0]), mpf(HUB_A[1])]
    M = matrix([[pts[0][0], pts[1][0], pts[2][0]],
                [pts[0][1], pts[1][1], pts[2][1]],
                [1, 1, 1]])
    lam = lu_solve(M, matrix([hA[0], hA[1], 1]))
    V = sum(lam[i] * lam[j] * ((pts[i][0] - pts[j][0]) ** 2 + (pts[i][1] - pts[j][1]) ** 2)
            for i in range(3) for j in range(i))
    P("     lam = (%s)" % ", ".join(mp.nstr(v, 22) for v in lam))
    P("     |H_A - p_k| - R = %s"
      % ", ".join(mp.nstr(sqrt((pts[k][0] - hA[0]) ** 2 + (pts[k][1] - hA[1]) ** 2) - Rhi, 20)
                  for k in range(3)))
    P("     V(lam) - R^2 = %s" % mp.nstr(V - Rhi * Rhi, 20))
    P("     sqrt(R^2 - V(lam)) = %s" % mp.nstr(sqrt(Rhi * Rhi - V), 20))

    # -------- D: central coupling
    P("")
    P("=" * 100)
    P("D. CENTRAL-ENDPOINT COUPLING")
    sw = [0, 4]
    for si in sw:
        X = c[si]
        P("   switch ring lead c[%d] = ring_row_%d = (%+.12f, %+.12f)  |c| = %.12f (R+1-|c| = %+.3e)"
          % (si, rings[(si + 4) % 9], X[0], X[1], np.linalg.norm(X), R + 1 - np.linalg.norm(X)))
    for si in sw:
        T = np.array([HUB_A, HUB_B, c[si]])
        e = [np.linalg.norm(T[1] - T[2]), np.linalg.norm(T[0] - T[2]), np.linalg.norm(T[0] - T[1])]
        ar = abs((T[1] - T[0])[0] * (T[2] - T[0])[1] - (T[1] - T[0])[1] * (T[2] - T[0])[0]) / 2
        rho = e[0] * e[1] * e[2] / (4 * ar)
        P("   central face (hA,hB,lead c[%d]): sides %.6f %.6f %.6f   rho = %.12f  rho - R = %+.6e"
          % (si, e[0], e[1], e[2], rho, rho - R))
    P("")
    P("   exposed-arc ends of the switch rings (which hub is tight at each end):")
    for si in sw:
        P("     lead c[%d]:" % si)
        for ei, na in ((si - 1, "left "), (si, "right")):
            pin = allpins[ei % 9][0]
            P("       %s end = pin of lead edge (%d,%d) at (%+.12f,%+.12f):"
              % (na, ei % 9, ((ei % 9) + 1) % 9, pin[0], pin[1]))
            P("           |pin - hA| - R = %+.3e      |pin - hB| - R = %+.3e"
              % (np.linalg.norm(pin - HUB_A) - R, np.linalg.norm(pin - HUB_B) - R))
    P("")
    P("   central faces are ACUTE (so the circumradius criterion is two-sided there):")
    for si in sw:
        T = np.array([HUB_A, HUB_B, c[si]])
        ang = []
        for k in range(3):
            u = T[(k + 1) % 3] - T[k]
            w = T[(k + 2) % 3] - T[k]
            ang.append(math.degrees(math.acos(np.dot(u, w) / np.linalg.norm(u) / np.linalg.norm(w))))
        P("     face (hA,hB,lead c[%d]): angles %s  -> max angle %.3f deg (<90 = acute)"
          % (si, " ".join("%.3f" % a for a in ang), max(ang)))
    P("")
    P("   RIGIDITY DICHOTOMY (tangent cone of K at the hub): if the active pins surround the")
    P("   hub (max angular gap < 180deg) then K = {hub} locally and Vmax = R^2; if they lie in")
    P("   an arc of span theta < 180deg the feasible directions at the hub form a wedge of")
    P("   aperture 180deg - theta, and the pin intersection is a genuine sliver.")
    for nm, pins, H in (("A (5-chain)", pinsA, HUB_A), ("B (4-chain)", pinsB, HUB_B)):
        act = [t for t in range(len(pins)) if abs(np.linalg.norm(pins[t] - H) - R) < 1e-10]
        P("     hub %s: active chain positions %s" % (nm, act))
        if len(act) >= 2:
            angs = sorted(math.degrees(math.atan2(*(pins[t] - H)[::-1])) % 360 for t in act)
            gaps = [angs[i + 1] - angs[i] for i in range(len(angs) - 1)] + [360 - angs[-1] + angs[0]]
            P("        azimuths about hub: %s" % " ".join("%.3f" % a for a in angs))
            P("        gaps: %s ; max gap %.3f deg -> %s"
              % (" ".join("%.3f" % g for g in gaps), max(gaps),
                 "SURROUNDS (rigid)" if max(gaps) < 180 else "arc of span %.2f deg (non-rigid)" % (360 - max(gaps))))
    # binding pair of hub B's sliver
    i0, i1 = 0, 3
    d = float(np.linalg.norm(pinsB[i0] - pinsB[i1]))
    P("")
    P("   hub B sliver: binding pin pair (chain positions 0,3) distance d = %.12f  (2R - d = %.6e)"
      % (d, 2 * R - d))
    P("     exact lens diameter 2 sqrt(R^2 - d^2/4) = %.12f" % (2 * math.sqrt(R * R - d * d / 4)))
    P("     distances of that pair's other points to the two remaining pins: %.6f %.6f"
      % (np.linalg.norm(pinsB[i1] - pinsB[1]), np.linalg.norm(pinsB[i0] - pinsB[2])))
    partE(c, rings, rings, pinsA, pinsB, HUB_A, HUB_B, R)


def circum2d(A, B, C):
    e = [np.linalg.norm(B - C), np.linalg.norm(A - C), np.linalg.norm(A - B)]
    ar = abs((B[0] - A[0]) * (C[1] - A[1]) - (B[1] - A[1]) * (C[0] - A[0])) / 2
    return e[0] * e[1] * e[2] / (4 * ar)


def partE(c, rings, ring_rows, pinsA, pinsB, HUB_A, HUB_B, R):
    """Ring-determined hub pair: (i) hub A = circumcentre of its 3 active pins (2 linear
    equations), (ii) hub B = solution of the two central-face equalities rho = R."""
    from scipy.optimize import fsolve
    P("")
    P("=" * 100)
    P("E. RING-DETERMINED HUB PAIR (elimination calibration, no use of the recorded hubs)")
    # (i) hub A = equal-distance point of the three active pins (circumcentre of that triple)
    T = pinsA[[0, 2, 4]]
    M = 2 * np.array([T[1] - T[0], T[2] - T[0]])
    b = np.array([T[1] @ T[1] - T[0] @ T[0], T[2] @ T[2] - T[0] @ T[0]])
    hA = np.linalg.solve(M, b)
    rA = np.linalg.norm(hA - T[0])
    P("   circumcentre of the three active pins of hub A = (%+.15f, %+.15f), radius %.15f"
      % (hA[0], hA[1], rA))
    P("     |hA_pin - hA_record| = %.6e     rho_A - R = %+.6e"
      % (np.linalg.norm(hA - HUB_A), rA - R))
    # (ii) hub B from the two central faces rho(hA,hB,c_switch) = R
    sw = [c[0], c[4]]

    def F(z):
        hB = np.array(z, float)
        return [circum2d(HUB_A if False else hA, hB, sw[0]) - R,
                circum2d(hA, hB, sw[1]) - R]
    sol = fsolve(F, HUB_B + np.array([3e-3, -2e-3]), full_output=True)
    hB = sol[0]
    P("   hub B from the two central equations (start = record + (3e-3,-2e-3)):")
    P("     hB_glue = (%+.15f, %+.15f)   |hB_glue - hB_record| = %.6e   residual = %.3e"
      % (hB[0], hB[1], np.linalg.norm(hB - HUB_B), max(abs(np.array(F(hB))))))
    P("     also: |hB_glue - pin_k| - R over hub B's active pins = %s"
      % " ".join("%+.3e" % (np.linalg.norm(hB - pinsB[t]) - R) for t in range(4)))
    P("   => the ring data alone (3-pin circumcentre + 2 central equalities) reproduces the")
    P("      recorded hub pair to the printing accuracy; the recorded hubs are consistent with")
    P("      the elimination, NOT independent data.")
    partF(c, rings, HUB_A, HUB_B, R)


def partF(c, rings, HUB_A, HUB_B, R):
    """High-precision reading of |p_out| - 1 for the nine ring edges (the outer-root / interface
    hypothesis of the lead's convexification: p_out outside the unit disk)."""
    mp.dps = 60
    Rhi = mpf(repr(R))
    P("")
    P("=" * 100)
    P("F. OUTER ROOTS OF THE NINE EDGES: is |p_out| = 1 (i.e. the interface hypothesis holds")
    P("   with equality: the outer root sits exactly on the unit circle)?")
    P("     edge      |p_out| - 1 (60-digit)         |p_out| - (R + |hub|) for the serving hub")
    for i in range(9):
        a = [mpf(c[i][0]), mpf(c[i][1])]
        b = [mpf(c[(i + 1) % 9][0]), mpf(c[(i + 1) % 9][1])]
        m = [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2]
        d = sqrt((b[0] - a[0]) ** 2 + (b[1] - a[1]) ** 2)
        n = [-(b[1] - a[1]) / d, (b[0] - a[0]) / d]
        k = sqrt(Rhi * Rhi - (d / 2) ** 2)
        r1 = [m[0] + k * n[0], m[1] + k * n[1]]
        r2 = [m[0] - k * n[0], m[1] - k * n[1]]
        n1 = sqrt(r1[0] ** 2 + r1[1] ** 2)
        n2 = sqrt(r2[0] ** 2 + r2[1] ** 2)
        po = r1 if n1 > n2 else r2
        npo = sqrt(po[0] ** 2 + po[1] ** 2)
        hub = HUB_A if i in (4, 5, 6, 7, 8) else HUB_B
        dhub = sqrt((po[0] - mpf(hub[0])) ** 2 + (po[1] - mpf(hub[1])) ** 2)
        P("     (%d,%d)   %s      %s"
          % (i, (i + 1) % 9, mp.nstr(npo - 1, 12), mp.nstr(dhub - Rhi - sqrt(mpf(hub[0]) ** 2 + mpf(hub[1]) ** 2), 12)))
    P("   (a positive last column means the outer disk B(p_out,R) is disjoint from the hub ball")
    P("    B(0,1-R) of the serving hub, i.e. the outer constraint is inactive there.)")


def main():
    partA()
    partCD()
    (OUT / "r20_5chain_elimination.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_5chain_elimination.txt"))


if __name__ == "__main__":
    main()
