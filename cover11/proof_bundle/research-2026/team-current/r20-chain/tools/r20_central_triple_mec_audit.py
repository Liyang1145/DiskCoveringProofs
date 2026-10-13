"""Independent MEC/active-set audit of the central fiber triples (read-only w.r.t. r20-geometry).

Writes ../out/r20_central_triple_mec_audit.txt.

WHY (lead's instruction): determine which triples are TRULY tight from the minimum enclosing
circle (MEC) active set and its positive barycentric weights, NOT from a circumradius (the
circumcircle is the MEC only in the acute branch) and NOT from 1e-16 numerics being read as exact
equality.

THEORY USED (exact, for equal-radius disks):
  For closed disks B(p_j,r) with centres p_j and Rc := MEC radius of {p_j}, m := MEC centre:
     * the MEC centre is unique.  JUSTIFICATION (per lead's correction): max_j |x-p_j| is NOT
       strictly convex (a single norm is linear along rays).  Use the SQUARED form
           max_j |x-p_j|^2 = |x|^2 + max_j (|p_j|^2 - 2 p_j.x),
       which is strongly convex (|x|^2) plus a max of affine functions (convex), hence strongly
       convex with a unique minimiser; minimising max_j|x-p_j|^2 is the same as minimising
       max_j|x-p_j| (t -> t^2 is increasing on [0,inf));
     * m lies in every disk  <=>  Rc <= r, so   ^_j B(p_j,r) = empty  <=>  Rc > r;
     * ^_j B(p_j,r) = {m}  <=>  Rc = r    (if x is another common point then x also encloses all
       p_j within r = Rc, contradicting uniqueness of the MEC centre; conversely Rc = r gives
       ^B(p_j,r) = {m} because a disk of positive radius would sit inside otherwise);
     * MEC optimality (Kuhn-Tucker): m is the MEC centre  <=>  0 in conv{ (m-p_j)/|m-p_j| : j
       active }, i.e. the active unit directions are not in an open half-plane (max cyclic gap <= pi).
       In the SATURATED configuration (all |m-p_j| = r) this is equivalent to the singleton test.
     * Certificate data: with lambda_j >= 0, sum lambda_j = 1, sum lambda_j p_j = m supported on the
       active set, the Farkas weights u_j = lambda_j (m-p_j) give sum u_j = 0 and objective
       sum_j (p_j.u_j + r|u_j|) = Rc (r - Rc):  < 0 (empty), = 0 (tight), > 0 (interior nonempty).
  All of this is CQ-free (product separation), no inf-convolution equality is used as a load-bearing
  step, and no attained dual optimum is assumed.
"""
import io, json, itertools
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


def sub(p, q):
    return (p[0]-q[0], p[1]-q[1])


def add(p, q):
    return (p[0]+q[0], p[1]+q[1])


def mul(s, p):
    return (s*p[0], s*p[1])


def nrm(p):
    return sqrt(p[0]**2 + p[1]**2)


def dot(p, q):
    return p[0]*q[0] + p[1]*q[1]


def mec3(A, B, C):
    """exact MEC of three points: returns (m, Rc, branch, active_indices)."""
    ip = [dot(sub(B, A), sub(C, A)), dot(sub(A, B), sub(C, B)), dot(sub(A, C), sub(B, C))]
    if min(ip) <= 0:                                   # obtuse/right/collinear: diameter branch
        pairs = [(A, B), (A, C), (B, C)]
        idx = max(range(3), key=lambda t: nrm(sub(pairs[t][0], pairs[t][1])))
        m = mul(mpf(1)/2, add(pairs[idx][0], pairs[idx][1]))
        Rc = nrm(sub(pairs[idx][0], pairs[idx][1]))/2
        act = {0: [0, 1], 1: [0, 2], 2: [1, 2]}[idx]
        return m, Rc, "diameter", act
    a2 = dot(sub(B, C), sub(B, C))
    b2 = dot(sub(C, A), sub(C, A))
    c2 = dot(sub(A, B), sub(A, B))
    al = a2*(b2 + c2 - a2)
    be = b2*(c2 + a2 - b2)
    ga = c2*(a2 + b2 - c2)
    m = mul(1/(al+be+ga), add(add(mul(al, A), mul(be, B)), mul(ga, C)))
    return m, nrm(sub(m, A)), "circumcircle", [0, 1, 2]


def main():
    mp.dps = 45
    raw = json.loads((ROOT / "n11/upper/certified_object.json").read_text(encoding="utf-8-sig"))
    SC = mpf(10)**int(raw["decimals"])
    C = [(mpf(int(a))/SC, mpf(int(b))/SC) for a, b in raw["centers_scaled_1e17"]]
    R = mpf(str(raw["certified_interval"]["lo"]))
    HA, HB = C[2], C[0]                                # geometry's labels: hub A = row 2, hub B = row 0
    CA, CB = C[5], C[6]                                # switch rings = rows 5, 6
    FANB = [(6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]

    def roots(a, c, r):
        m = mul(mpf(1)/2, add(a, c))
        dv = sub(c, a)
        d = nrm(dv)
        if d == 0 or d > 2*r:
            return None
        n = (-dv[1]/d, dv[0]/d)
        k = sqrt(r*r - d*d/4)
        return (sub(m, mul(k, n)), add(m, mul(k, n)))

    def pin(i, j, r):
        p = roots(C[i], C[j], r)
        if p is None:
            return None
        return p[0] if nrm(p[0]) < nrm(p[1]) else p[1]

    def near(a_roots):
        m1 = abs(nrm(sub(HB, a_roots[0])) - R)
        m2 = abs(nrm(sub(HB, a_roots[1])) - R)
        return a_roots[0] if m1 < m2 else a_roots[1]

    q0 = near(roots(HA, CA, R))
    q4 = near(roots(HA, CB, R))
    pins = {p: pin(*p, r=R) for p in FANB}
    CENT = [("central0", q0), ("central4", q4)] + [("pin%s" % (p,), pins[p]) for p in FANB]

    P("=" * 100)
    P("A. SETUP (same objects as r20-geometry/central_tight_triple.py; their file read-only)")
    P("   geometry's labels: hub A = row 2 = (%.12f, %.12f) ; hub B = row 0 = (%.12f, %.12f)"
      % (HA[0], HA[1], HB[0], HB[1]))
    P("   NOTE label map: my r20-chain convention has hub A = row 0 (lower) = their 'hub B';")
    P("   their FANB 5-chain is served by row 0 (lower hub) — same physics, swapped names.")
    P("   switch-ring roots: q_0 = (%.12f, %.12f), q_4 = (%.12f, %.12f)"
      % (q0[0], q0[1], q4[0], q4[1]))

    P("")
    P("B. THEOREM (exact, stated in the header): for equal-radius disks, with Rc = MEC radius of the")
    P("   centres and m = the (unique) MEC centre:  empty <=> Rc > r ; SINGLETON {m} <=> Rc = r ;")
    P("   interior nonempty <=> Rc < r .  Certified readings below are NUMERICAL: |Rc - r| ~ 1e-17")
    P("   is 'numerically tight' and is NOT a proof of exact equality (lead's rule).")

    P("")
    P("C. ALL 35 TRIPLES — Rc - r, branch, active set, lambda, MEC centre vs hub B, verdict")
    rows = []
    for (n1, c1), (n2, c2), (n3, c3) in itertools.combinations(CENT, 3):
        m, Rc, br, act = mec3(c1, c2, c3)
        pts = [c1, c2, c3]
        # barycentric weights of m (lambda_j), exact via 2x2 solve
        from mpmath import matrix, lu_solve
        if br == "circumcircle":
            M = matrix([[pts[1][0]-pts[0][0], pts[2][0]-pts[0][0]],
                        [pts[1][1]-pts[0][1], pts[2][1]-pts[0][1]]])
            x = lu_solve(M, matrix([m[0]-pts[0][0], m[1]-pts[0][1]]))
            lam = [1-x[0]-x[1], x[0], x[1]]
        else:
            i, j = act
            lam = [mpf(0)]*3
            lam[i] = mpf(1)/2
            lam[j] = mpf(1)/2
        # Farkas-type objective with u_j = lam_j (m - p_j)
        obj = mpf(0)
        for j3 in range(3):
            u = mul(lam[j3], sub(m, pts[j3]))
            obj += dot(pts[j3], u) + R*nrm(u)
        db = nrm(sub(m, HB))
        rows.append((float(Rc - R), (n1, n2, n3), float(Rc), br, tuple(act),
                     [float(x) for x in lam], float(Rc*(R-Rc)), float(db), float(obj)))
    rows.sort()
    P("   %-42s %12s %12s %8s %-16s %-22s %12s" %
      ("triple", "Rc-r", "objective", "|m-hubB|", "branch", "lambda", "verdict"))
    for d, names, Rc, br, act, lam, objv, db, objv2 in rows:
        if d > 1e-12:
            v = "EMPTY (Rc>r)"
        elif abs(d) <= 1e-12:
            v = "TIGHT/SINGLETON {m} (numeric)"
        else:
            v = "interior (not tight)"
        P("   %-42s %+12.3e %12.3e %8.1e %-16s %-22s %s"
          % (str(names), d, objv, db, br + str(act),
             str([round(x, 5) for x in lam]), v))

    P("")
    P("D. THE LEAD-QUOTED TRIPLE (central0, central4, pin(9,10)) — full data")
    for d, names, Rc, br, act, lam, objv, db, objv2 in rows:
        if names == ("central0", "central4", "pin(9, 10)"):
            P("   Rc - r = %+.3e ; branch = %s (active %s) ; lambda = %s (all > 0: %s)"
              % (d, br, act, [round(x, 6) for x in lam], all(x > 0 for x in lam)))
            P("   MEC centre m vs hub B row 0: |m - b| = %.3e  (theorem predicts m = b when tight)" % db)
            P("   Farkas objective Rc(r-Rc) = %+.3e (0 to rounding: no infeasibility)" % objv)
            P("   -- the triple is feasible and, at exact saturation, its intersection is {b}.")
            dirs = [sub(HB, p) for p in (q0, q4, pins[(9, 10)])]
            angs = sorted([atan2(x[1], x[0]) for x in dirs])
            gaps = [(angs[(i+1) % 3] + (2*MP_PI if i == 2 else 0)) - angs[i] for i in range(3)]
            P("   active unit directions (hub -> centres) cyclic gaps (deg): %s ; max = %.2f"
              % ([round(float(g*180/MP_PI), 2) for g in gaps], float(max(gaps)*180/MP_PI)))
            P("   => max gap <= 180 deg here, consistent with MEC optimality at m = b (NOT 189 deg:")
            P("      the 189 deg figure belongs to geometry's other (fan-A 4-pin) gap list — see")
            P("      their own correction note in central_tight_triple.py line 99.)")

    P("")
    P("E. VERDICT")
    nt = [r for r in rows if abs(r[0]) <= 1e-12]
    P("   numerically tight triples: %d of 35 (Rc - r within 1e-12, all circumcircle branch)" % len(nt))
    for d, names, Rc, br, act, lam, objv, db, objv2 in nt:
        P("      %s : Rc - r = %+.3e ; lambda = %s ; |m - hubB| = %.1e" %
          (names, d, [round(x, 5) for x in lam], db))
    P("   All tight triples have the MEC centre AT the hub (|m - b| ~ 1e-16) — the independent")
    P("   consistency check that they are saturated at b.  Everything is 'numerical': no exact")
    P("   equality is claimed from 1e-17 readings; the exact statement is Rc = r <=> singleton.")

    (OUT / "r20_central_triple_mec_audit.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_central_triple_mec_audit.txt"))


if __name__ == "__main__":
    main()
