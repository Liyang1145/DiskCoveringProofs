"""Chain-endpoint shape derivative under central-preserving hub variation (lead task 2026-09-25).

Read-only outside r20-chain; writes ../out/r20_endpoint_shape_derivative.txt.

QUANTIFIERS (fixed first, as requested)
  Data: r = certified_interval.lo; the nine rings of the record object (lead index space); the chain
  assignment (hub A serves lead edges 4..8, hub B serves lead edges 0..3); the two central faces
  (hA,hB,lead c[0]) and (hA,hB,lead c[4]) with switch rings row 5 and row 6.
  Family: FIXED hub hA and all ring centres except one switch ring; VARY t -> c_sw(t) = c_sw(0) + t d
  (several directions d) and SIMULTANEOUSLY hB(t), determined by imposing BOTH central faces TIGHT:
        rho(hA, hB(t), c_5) = r   and   rho(hA, hB(t), c_6(t)) = r      (2 eqs, 2 unknowns)
  (if the moved ring is c_5, the equations are rho(hA,hB,c_5(t)) = r and rho(hA,hB,c_6) = r).
  Constraints monitored along the family (no grids: local derivatives only):
     chain margins  M_A := r^2 - Vmax(A-chain pins),  M_B := r^2 - Vmax(B-chain pins),
     annulus of the moved ring, support functions of the hub-feasible bodies K = ^ B(p_k, r),
     central-face circumradii, |hA - hB|.

CANDIDATES TESTED (each with its local derivative at t = 0):
  C1  M_A, M_B (chain feasibility margins; <= 0 at the record object for the A chain)
  C2  the rotation slack S := sum_chain(s_i + s_{i+1}) - sum_chain theta_i (>= 0 by the transfer map)
  C3  the hub-feasible support functions h_K(u) = min_k (<p_k,u> + r) of each chain's pin body
  C4  |hA - hB| and the central-face margins rho - r
A candidate monotone quantity for the global argument must have a definite sign of its t-derivative
that is FORCED by the central constraints (i.e. the direction that decreases the margin must be
blocked by another constraint).  The script reports signs, not certificates.

All derivatives: Richardson-extrapolated central differences at 40-digit precision (mpmath).
"""
import json, math
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


# ---------------------------------------------------------------- basic geometry (mpmath)
def circ2(A, B, C):
    a = (B[0]-C[0])**2 + (B[1]-C[1])**2
    b = (A[0]-C[0])**2 + (A[1]-C[1])**2
    c = (A[0]-B[0])**2 + (A[1]-B[1])**2
    cr = (B[0]-A[0])*(C[1]-A[1]) - (B[1]-A[1])*(C[0]-A[0])
    if cr == 0:
        return mpf('inf')
    return sqrt(a*b*c/(4*cr*cr))


def pin(a, b, r):
    """inner (min-norm) root of the pair a,b."""
    m = [(a[0]+b[0])/2, (a[1]+b[1])/2]
    d = sqrt((b[0]-a[0])**2 + (b[1]-a[1])**2)
    n = [-(b[1]-a[1])/d, (b[0]-a[0])/d]
    k = sqrt(r*r - (d/2)**2)
    p1 = [m[0]+k*n[0], m[1]+k*n[1]]
    p2 = [m[0]-k*n[0], m[1]-k*n[1]]
    if p1[0]**2+p1[1]**2 < p2[0]**2+p2[1]**2:
        return p1
    return p2


def Vmax(pins):
    """max over the simplex of V(lam) (pairs and 3-supports with interior circumcentre)."""
    m = len(pins)
    best = mpf(-1)
    for i in range(m):
        for j in range(i+1, m):
            v = ((pins[i][0]-pins[j][0])**2 + (pins[i][1]-pins[j][1])**2)/4
            if v > best:
                best = v
    for i in range(m):
        for j in range(i+1, m):
            for k in range(j+1, m):
                A, B, C = pins[i], pins[j], pins[k]
                cr = (B[0]-A[0])*(C[1]-A[1]) - (B[1]-A[1])*(C[0]-A[0])
                if cr == 0:
                    continue
                a2 = (B[0]-C[0])**2 + (B[1]-C[1])**2
                b2 = (A[0]-C[0])**2 + (A[1]-C[1])**2
                c2 = (A[0]-B[0])**2 + (A[1]-B[1])**2
                rho2 = a2*b2*c2/(4*cr*cr)
                # circumcentre, barycentric coords
                # circumcentre O: 2(B-A).O = |B|^2-|A|^2 , 2(C-A).O = |C|^2-|A|^2
                A1 = matrix([[2*(B[0]-A[0]), 2*(B[1]-A[1])], [2*(C[0]-A[0]), 2*(C[1]-A[1])]])
                b1 = matrix([B[0]**2+B[1]**2-A[0]**2-A[1]**2, C[0]**2+C[1]**2-A[0]**2-A[1]**2])
                O = lu_solve(A1, b1)
                # barycentric: x(B-A) + y(C-A) = O - A
                A2 = matrix([[B[0]-A[0], C[0]-A[0]], [B[1]-A[1], C[1]-A[1]]])
                b2 = matrix([O[0]-A[0], O[1]-A[1]])
                x = lu_solve(A2, b2)
                lam = [1-x[0]-x[1], x[0], x[1]]
                if min(lam) >= -mpf('1e-25'):
                    if rho2 > best:
                        best = rho2
    return best


def main():
    mp.dps = 40
    raw = json.loads(OBJ.read_text(encoding="utf-8-sig"))
    R = mpf(str(raw["certified_interval"]["lo"]))
    C = [[mpf(int(a))/10**17, mpf(int(b))/10**17] for a, b in raw["centers_scaled_1e17"]]
    rings = sorted([i for i in range(11) if i not in (0, 2)],
                   key=lambda i: math.atan2(float(C[i][1]), float(C[i][0])))
    # RESOLVED lead mapping: shift=4, swap=1  (see out/audit_lead_q0_map.txt)
    Cbase = [C[rings[i]] for i in range(9)] + [C[0], C[2]]
    idx = [(i + 4) % 9 for i in range(9)] + [10, 9]
    c = [Cbase[j] for j in idx]
    HA, HB = c[10], c[9]                                      # c[10] = row 0 = hub A
    chainA = [4, 5, 6, 7, 8]
    chainB = [0, 1, 2, 3]
    P("=" * 100)
    P("QUANTIFIERS (fixed)")
    P("  r = %s" % mp.nstr(R, 20))
    P("  hub A = c[10] = row 0 ; hub B = c[9] = row 2 ; chains: A = lead edges 4..8, B = 0..3")
    P("  central faces: (hA,hB,row5) = (c[10],c[9],c[0]) and (hA,hB,row6) = (c[10],c[9],c[4])")
    P("  family: hA fixed, all rings fixed except one switch ring c_sw(t) = c_sw(0) + t*d,")
    P("          hB(t) chosen on the SAME branch of {both central circumradii = r} (closed-form")
    P("          circle-pair intersections of the tight sets, branch-tracked by continuity).")

    def tight_centres(A, B, Rr):
        """the two centres of radius-Rr circles through A and B."""
        M = [(A[0]+B[0])/2, (A[1]+B[1])/2]
        d = sqrt((B[0]-A[0])**2 + (B[1]-A[1])**2)
        n = [-(B[1]-A[1])/d, (B[0]-A[0])/d]
        k = sqrt(Rr*Rr - (d/2)**2)
        return [[M[0]+k*n[0], M[1]+k*n[1]], [M[0]-k*n[0], M[1]-k*n[1]]]

    def circle_isect(q1, q2, Rr):
        d = sqrt((q2[0]-q1[0])**2 + (q2[1]-q1[1])**2)
        if d > 2*Rr:
            return []
        if d == 0:
            return []
        M = [(q1[0]+q2[0])/2, (q1[1]+q2[1])/2]
        n = [-(q2[1]-q1[1])/d, (q2[0]-q1[0])/d]
        h = sqrt(max(Rr*Rr - d*d/4, mpf(0)))
        return [[M[0]+h*n[0], M[1]+h*n[1]], [M[0]-h*n[0], M[1]-h*n[1]]]

    def solve_hB(hA, cs, hb_prev):
        """hB with rho(hA,hB,row5)=r and rho(hA,hB,row6)=r, on the branch near hb_prev."""
        cands = []
        for qa in tight_centres(hA, cs[0], R):
            for qb in tight_centres(hA, cs[4], R):
                cands += circle_isect(qa, qb, R)
        if not cands:
            return None
        return min(cands, key=lambda p: (p[0]-hb_prev[0])**2 + (p[1]-hb_prev[1])**2)

    def config(t, moved, d, hb_prev):
        cs = [list(x) for x in c]
        cs[moved] = [c[moved][0] + t*d[0], c[moved][1] + t*d[1]]
        hb = solve_hB(cs[10], cs, hb_prev)
        return cs, hb

    def observables(t, moved, d, hb_prev):
        cs, hb = config(t, moved, d, hb_prev)
        pins = {}
        for i in range(9):
            pins[i] = pin(cs[i], cs[(i+1) % 9], R)
        VA = Vmax([pins[i] for i in chainA])
        VB = Vmax([pins[i] for i in chainB])
        out = {}
        out["M_A"] = R*R - VA
        out["M_B"] = R*R - VB
        for nm, H, ch in (("A", cs[10], chainA), ("B", hb, chainB)):
            S = mpf(0)
            for i in ch:
                a, b = cs[i], cs[(i+1) % 9]
                d1 = sqrt((a[0]-H[0])**2+(a[1]-H[1])**2)
                d2 = sqrt((b[0]-H[0])**2+(b[1]-H[1])**2)
                s1 = mp.acos(min(mpf(1), d1/(2*R)))
                s2 = mp.acos(min(mpf(1), d2/(2*R)))
                v1 = [a[0]-H[0], a[1]-H[1]]; v2 = [b[0]-H[0], b[1]-H[1]]
                cs_t = (v1[0]*v2[0]+v1[1]*v2[1])/(d1*d2)
                th = mp.acos(max(mpf(-1), min(mpf(1), cs_t)))
                S += s1 + s2 - th
            out["slack" + nm] = S
        # TRUE support h_K(u) of K = ^ B(p_k,r) via FINITE BOUNDARY CANDIDATES (arc points with
        # normal u/|u|, plus pairwise circle intersections).  WITHDRAWN: the earlier "min-h
        # selector" h_K = min_k(<p_k,u> + r|u|) — that is only an UPPER BOUND and is strict in
        # general (lead's calibration: two unit disks at (+-1/2,0), u vertical: min-h = 1 but
        # h_K = sqrt(3)/2).  We now record both, clearly labelled.
        for nm, ch in (("A", chainA), ("B", chainB)):
            for u in ([mpf(1), mpf(0)], [mpf(0), mpf(1)], [mpf(1)/sqrt(2), mpf(1)/sqrt(2)]):
                uf = [float(u[0]), float(u[1])]
                nu = sqrt(u[0]*u[0] + u[1]*u[1])
                hmin = min(pins[i][0]*u[0] + pins[i][1]*u[1] + R*nu for i in ch)
                cand = [[pins[i][0] + R*u[0]/nu, pins[i][1] + R*u[1]/nu] for i in ch]
                for a in range(len(ch)):
                    for b in range(a+1, len(ch)):
                        q1, q2 = pins[ch[a]], pins[ch[b]]
                        dd = sqrt((q2[0]-q1[0])**2 + (q2[1]-q1[1])**2)
                        if dd > 2*R or dd == 0:
                            continue
                        mx, my = (q1[0]+q2[0])/2, (q1[1]+q2[1])/2
                        nx, ny = -(q2[1]-q1[1])/dd, (q2[0]-q1[0])/dd
                        hh = sqrt(max(R*R - dd*dd/4, mpf(0)))
                        cand.append([mx+hh*nx, my+hh*ny]); cand.append([mx-hh*nx, my-hh*ny])
                best = None
                for x in cand:
                    if all((x[0]-pins[i][0])**2 + (x[1]-pins[i][1])**2 <= R*R*mpf('1.0000001')
                           for i in ch):
                        v = x[0]*u[0] + x[1]*u[1]
                        if best is None or v > best:
                            best = v
                out["hK%s_%.2f_%.2f" % (nm, uf[0], uf[1])] = best if best is not None else mpf('nan')
                out["hmin%s_%.2f_%.2f" % (nm, uf[0], uf[1])] = hmin     # upper bound only
        out["distAB"] = sqrt((cs[10][0]-hb[0])**2 + (cs[10][1]-hb[1])**2)
        out["rho_c5"] = circ2(cs[10], hb, cs[0])
        out["rho_c6"] = circ2(cs[10], hb, cs[4])
        out["L_sw"] = sqrt(cs[moved][0]**2 + cs[moved][1]**2)
        return out

    hb0 = HB
    hb_chk = solve_hB(HA, c, HB)
    P("  hub B re-solved from both central equalities: (%s, %s) ; |solved - record| = %s"
      % (mp.nstr(hb_chk[0], 18), mp.nstr(hb_chk[1], 18),
         mp.nstr(sqrt((hb_chk[0]-HB[0])**2 + (hb_chk[1]-HB[1])**2), 6)))
    hb0 = hb_chk

    def deriv(moved, d, key, h=mpf('1e-4')):
        fs = {}
        for tt in (h, -h, 2*h, -2*h):
            fs[tt] = observables(tt, moved, d, hb_chk)[key]
        d1 = (fs[h]-fs[-h])/(2*h)
        d2 = (fs[2*h]-fs[-2*h])/(4*h)
        return (4*d1-d2)/3

    base = observables(mpf(0), 4, [mpf(0), mpf(0)], hb_chk)
    P("")
    P("BASE (record object, constrained family at t = 0):")
    for k in sorted(base):
        P("   %-22s %s" % (k, mp.nstr(base[k], 18)))

    P("")
    P("CANDIDATE DERIVATIVES  d/dt at t = 0   (moved ring, direction)")
    for moved, nm in ((4, "c[4]=row6"), (0, "c[0]=row5")):
        Ldir = [c[moved][0], c[moved][1]]
        nrm = sqrt(Ldir[0]**2 + Ldir[1]**2)
        radial = [Ldir[0]/nrm, Ldir[1]/nrm]
        tangent = [-radial[1], radial[0]]
        for dnm, d in (("radial-out", radial), ("radial-in", [-radial[0], -radial[1]]),
                       ("tangential+", tangent), ("tangential-", [-tangent[0], -tangent[1]])):
            keys = ["M_A", "M_B", "slackA", "slackB", "distAB", "L_sw"]
            if moved == 0:
                keys.append("hKB_1.00_0.00")
            else:
                keys.append("hKB_1.00_0.00")
            row = []
            for k in keys:
                if k in base:
                    row.append("%s:%+.3e" % (k, float(deriv(moved, d, k))))
            P("   %s %-13s %s" % (nm, dnm, "  ".join(row)))
    P("")
    P("Legend: M_A/M_B = r^2 - Vmax(chain pins) (chain feasibility margins) — NUMERIC READINGS of a")
    P("rounded object: M_A = 3.5e-17 is *numerically zero*, NOT proven exactly zero, and NO")
    P("zero-tolerance / finite-allowance statement is made (first derivatives with unbounded")
    P("Taylor remainder cannot bound an excursion; see lead's correction).")
    P("slackA/B = rotation slack sum(s_i+s_{i+1}) - sum theta_i (bookkeeping; NOT monotone).")
    P("distAB = |hA-hB|; rho_c5/c6 = central circumradii (held = r by construction).")
    P("hK* = TRUE support of the pin body (finite boundary candidates: arc points with normal u/|u|")
    P("      plus pairwise circle intersections); hmin* = min_k(<p_k,u> + r|u|) is ONLY AN UPPER")
    P("      BOUND (strict in general; lead's calibration: two unit disks at (+-1/2,0), u vertical:")
    P("      min = 1 vs h_K = sqrt(3)/2).  The former 'support selector' rows are WITHDRAWN; the")
    P("      correct shape derivative is d h_K/d p_j = u_j^* (dual weights, split at vertices) —")
    P("      see out/r20_dual_support.txt.")
    P("Signs only - no certificate claimed.")

    (OUT / "r20_endpoint_shape_derivative.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_endpoint_shape_derivative.txt"))


if __name__ == "__main__":
    main()
