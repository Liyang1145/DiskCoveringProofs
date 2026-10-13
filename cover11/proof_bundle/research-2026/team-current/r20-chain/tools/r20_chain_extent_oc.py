"""r20 chain-extent OPTIMAL CONTROL formulation (hub eliminated by a running-region state).

Writes ../out/r20_chain_extent_oc.txt.  Read-only outside r20-chain.

CONTEXT (lead's task): the first hub's 5-pin chain condition MEC(p_1..p_5) <= r contains no hub
variable.  Question: can it be turned into a ring-only angular-span sharp bound conditioned on the
two endpoint ring centres, and can the interior 3-4 rings be ELIMINATED?  We must NOT assume that
every fan is tight (lead's FIXED-ENDPOINT-SATURATION counterexample: the internal ring can be pinned
with BOTH fans strictly slack).  Budget: one analytic route + one counterexample attack, no big grid.

FORMULATION (exact state / transition / domain)
  Data:      r; the m+1 = 6 ring centres c_1..c_6 of the chain (arc-ordered), with c_1, c_6 the
             two endpoint rings FIXED (the conditioning); the ring domain
                 D_ring = { c : 1-r <= |c| <= L* = sqrt(1-r^2) }        (C464 canonical domain)
             plus, when used for a COVER, the ordering/contiguity condition on the boundary arcs.
  Control:   c_{i+1} in D_ring (i = 1..m-1), the interior rings; c_1, c_{m+1} fixed.
  Pin map:   p_i = Pin(c_i, c_{i+1}) = the INNER root of the two radius-r circles through the pair
             (defined iff |c_i - c_{i+1}| <= 2r; inner = smaller norm).
  State:     (c_i, K_i) with K_i = ^_{j<=i} B(p_j, r)   (the running HUB BODY: the set of hubs that
             can still serve the prefix).  K_i is convex, nonempty iff MEC(p_1..p_i) <= r.
  Transition: K_{i+1} = K_i ^ B(p_{i+1}, r);  feasible iff K_{i+1} != empty.
  Why this covers ALL slack branches: the future of the chain depends on the past only through
  (c_i, K_i) — future pins involve c_i and future rings, and future feasibility is
  K_i ^ (future pin disks) != empty.  K_i is carried as a REGION, never as a point or an equality:
  a configuration whose fans are all strictly slack simply has a hub strictly inside K_i, and the
  counterexample above (pinned internal ring, both fans slack) is a perfectly admissible state.
  So no tightness normal form is assumed; slack branches are part of the state space.
  Value:     V_i(c_i, K_i) = max over the remaining interior rings of the chosen extent functional,
             with V_{m+1}(c_{m+1}, K_{m+1}) = 0; exact DP by the principle of optimality.

TWO EXTENT FUNCTIONALS (both ring-only; the interior rings enter differently)
  (E1) COVERED-ARC MEASURE (the arc of the unit circle covered by the chain's ring disks).
       Theorem (contiguity hypothesis): if the union of the ring arcs is contiguous — which is what
       a COVER of the boundary forces for a chain serving a connected piece of boundary — then
           span = (az_{m+1} + beta(|c_{m+1}|)) - (az_1 - beta(|c_1|)),
       i.e. the interior rings CANCEL EXACTLY: the covered measure is determined by the endpoints
       alone.  This is an identity, not an inequality — it eliminates the interior rings but yields
       no bound beyond the endpoints, and (see the counterexample attack) it FAILS without
       contiguity.
  (E2) TURN SPAN about a hub H in K_{m+1}:  Theta(H) = sum_i theta_i(H), theta_i the angle at H
       between the spokes to c_i, c_{i+1}.  This is the interior-dependent quantity that actually
       enters the two-hub rotation accounting (2*pi per hub).  Transfer map gives the per-step bound
           |s_i - s_{i+1}| <= theta_i <= s_i + s_{i+1},   s_i = arccos(|H-c_i|/(2r)),
       hence  Theta(H) <= s_1 + s_{m+1} + 2 * sum_{interior} s_i.   The DP for (E2) therefore
       reduces to
           maximise  sum_{interior rings} s_i(c_i, H)   subject to  K_{m+1} != empty,
       i.e. push the interior rings as FAR from the hub as legality allows while the running hub
       body stays nonempty.  The cap above is attained (all turns at their upper endpoint) exactly
       when the adjacent spokes are equal, i.e. on the "all-tight" branch of the transfer map.

ANALYTIC ROUTE (one): bound sum_interior s_i by a function of the two endpoints.
  Since s_i = arccos(|H - c_i|/(2r)) decreases in |H - c_i|, maximising sum s_i means maximising
  the ring-hub distances.  Legality only requires K_{m+1} != empty, so the extremal configuration
  has MEC(p_1..p_m) = r exactly (the hub pins all the pin disks: K = {m} = {H}), by compactness of
  the admissible set plus monotonicity: if all |H - c_i| could be increased simultaneously with
  K still nonempty, the value would rise.  At the extremum every pin satisfies |H - p_j| = r, i.e.
  every edge is TIGHT in the pin relaxation (F3'), so the extremal configuration is a tight one —
  while the lead's counterexample shows that this does NOT imply every admissible configuration can
  be DEFORMED to it.  The endpoint-conditioned bound is therefore
        Theta_max(c_1, c_{m+1}) = s_1 + s_{m+1} + 2 * max{ sum_interior s_i : K != empty },
  and the remaining content is the interior maximum, which is a convex (hence boundary-attained)
  problem in the interior ring positions.

COUNTEREXAMPLE ATTACK (one): the contiguity hypothesis in (E1) cannot be dropped, so the
"endpoint-determined span" is NOT a ring-only identity for arbitrary legal chains.  We exhibit a
legal 3-ring chain (all pin disks have a common hub) whose two outer arcs are disjoint and the
covered measure therefore exceeds the endpoints' own span.  This is a genuine attack on the naive
reading of the lead's question; it is NOT a counterexample to the DP (the DP's state (c_i,K_i)
tracks the slack correctly).
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


def pin_of(a, b, r):
    mx, my = (a[0]+b[0])/2, (a[1]+b[1])/2
    d = sqrt((b[0]-a[0])**2 + (b[1]-a[1])**2)
    if d == 0 or d > 2*r:
        return None
    nx, ny = -(b[1]-a[1])/d, (b[0]-a[0])/d
    k = sqrt(r*r - d*d/4)
    p1 = (mx + k*nx, my + k*ny)
    p2 = (mx - k*nx, my - k*ny)
    return p1 if (p1[0]**2 + p1[1]**2) < (p2[0]**2 + p2[1]**2) else p2


def mec3(A, B, C):
    def sub(p, q):
        return (p[0]-q[0], p[1]-q[1])
    def dot(p, q):
        return p[0]*q[0]+p[1]*q[1]
    def nrm(p):
        return sqrt(dot(p, p))
    ip = [dot(sub(B, A), sub(C, A)), dot(sub(A, B), sub(C, B)), dot(sub(A, C), sub(B, C))]
    if min(ip) <= 0:
        pairs = [(A, B), (A, C), (B, C)]
        idx = max(range(3), key=lambda t: nrm(sub(pairs[t][0], pairs[t][1])))
        m = ((pairs[idx][0][0]+pairs[idx][1][0])/2, (pairs[idx][0][1]+pairs[idx][1][1])/2)
        return nrm(sub(m, A)), m, "diameter"
    a2 = dot(sub(B, C), sub(B, C)); b2 = dot(sub(C, A), sub(C, A)); c2 = dot(sub(A, B), sub(A, B))
    al = a2*(b2+c2-a2); be = b2*(c2+a2-b2); ga = c2*(a2+b2-c2)
    m = ((al*A[0]+be*B[0]+ga*C[0])/(al+be+ga), (al*A[1]+be*B[1]+ga*C[1])/(al+be+ga))
    return nrm(sub(m, A)), m, "circumcircle"


def mec_pts(pts):
    """MEC of up to 5 points by the standard incremental (exact) algorithm on 2-3 active points."""
    if len(pts) == 1:
        return mpf(0), pts[0], "point"
    best = None
    n = len(pts)
    for i in range(n):
        for j in range(i+1, n):
            m = ((pts[i][0]+pts[j][0])/2, (pts[i][1]+pts[j][1])/2)
            R = sqrt((pts[i][0]-pts[j][0])**2 + (pts[i][1]-pts[j][1])**2)/2
            if all(sqrt((p[0]-m[0])**2 + (p[1]-m[1])**2) <= R + mpf('1e-30') for p in pts):
                if best is None or R < best[0]:
                    best = (R, m, "diameter")
    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                R, m, br = mec3(pts[i], pts[j], pts[k])
                if all(sqrt((p[0]-m[0])**2 + (p[1]-m[1])**2) <= R + mpf('1e-30') for p in pts):
                    if best is None or R < best[0]:
                        best = (R, m, "circumcircle")
    return best


def u_arc(c, r):
    """half-width of the arc of the unit circle covered by B(c,r) (canonical domain)."""
    nrm = sqrt(c[0]**2 + c[1]**2)
    val = (1 + nrm*nrm - r*r)/(2*nrm)
    val = min(mpf(1), max(mpf(-1), val))
    return acos(val)


def main():
    mp.dps = 40
    raw = json.loads((ROOT / "n11/upper/certified_object.json").read_text(encoding="utf-8-sig"))
    R = mpf(str(raw["certified_interval"]["lo"]))
    P("=" * 100)
    P("A. STATE / TRANSITION / DOMAIN (exact statements; see the docstring)")
    P("   r = %s" % mp.nstr(R, 20))
    P("   domain D_ring: 1-r <= |c| <= L* = sqrt(1-r^2); endpoints c_1, c_{m+1} fixed (the conditioning)")
    P("   pin map p_i = Pin(c_i,c_{i+1}) (inner root; exists iff |c_i-c_{i+1}| <= 2r)")
    P("   state (c_i, K_i), K_i = ^_{{j<=i}} B(p_j,r);  transition K_{i+1} = K_i ^ B(p_{i+1},r)")
    P("   optimality principle: future depends on the past only via (c_i, K_i) => DP is exact")
    P("   slack coverage: K_i is a REGION (never a point/equality); all-slack fan configurations")
    P("   (lead's counterexample: pinned internal ring, both fans slack) are admissible states.")

    P("")
    P("B. INSTANTIATION on the record 5-chain (hub A's chain; lead edge order 4..8)")
    m = 5
    # rings of the 5-chain in arc order: lead c[4],c[5],c[6],c[7],c[8],c[0]
    rings = [(4, 5), (5, 6), (6, 7), (7, 8), (8, 0)]
    c_all = [[mpf(int(a))/mpf(10)**int(raw["decimals"]), mpf(int(b))/mpf(10)**int(raw["decimals"])]
             for a, b in raw["centers_scaled_1e17"]]
    # resolved mapping: c[i] = C[rings[(i+4)%9]] for i<9, c[9] = C[10], c[10] = C[9]
    rr = sorted([i for i in range(11) if i not in (0, 2)],
                key=lambda i: math.atan2(float(c_all[i][1]), float(c_all[i][0])))
    Cbase = [c_all[rr[i]] for i in range(9)] + [c_all[0], c_all[2]]
    idx = [(i + 4) % 9 for i in range(9)] + [10, 9]
    c = [Cbase[j] for j in idx]
    chain_rings = [c[4], c[5], c[6], c[7], c[8], c[0]]
    pins_prefix = []
    P("   prefix   pin              MEC(prefix pins)-r      |K| proxy (max_j |MEC-p_j|)   verdict")
    for i in range(m):
        a, b = chain_rings[i], chain_rings[i+1]
        p = pin_of(a, b, R)
        pins_prefix.append(p)
        if len(pins_prefix) == 1:
            Rc, mm, br = mpf(0), p, "point"
        else:
            Rc, mm, br = mec_pts(pins_prefix)
        slack = Rc - R
        P("   %d pins   (%.9f,%.9f)  MEC - r = %+.3e  branch=%-12s  %s"
          % (i+1, p[0], p[1], float(slack), br,
             "FEASIBLE" if slack <= 1e-12 else "INFEASIBLE"))
    # endpoints
    c1, c6 = chain_rings[0], chain_rings[-1]
    P("   endpoints: az_1 = %.6f deg, beta_1 = %.6f deg ; az_6 = %.6f deg, beta_6 = %.6f deg"
      % (float(atan2(c1[1], c1[0])*180/MP_PI), float(u_arc(c1, R)*180/MP_PI),
         float(atan2(c6[1], c6[0])*180/MP_PI), float(u_arc(c6, R)*180/MP_PI)))
    az1 = atan2(c1[1], c1[0])
    az6 = atan2(c6[1], c6[0])
    if az6 < az1:                       # the chain wraps at +-pi
        az6 = az6 + 2*MP_PI
    spanE1 = (az6 + u_arc(c6, R)) - (az1 - u_arc(c1, R))
    P("   (E1) endpoint-determined covered-arc span = (az_6+beta_6)-(az_1-beta_1) = %.9f rad = %.3f deg"
      % (float(spanE1), float(spanE1*180/MP_PI)))
    # E2 cap with the actual hub (row 0 lower hub = my hub A)
    H = c[10]
    P("   (E2) hub H = (%.9f, %.9f) ; |H| = %.9f" % (H[0], H[1], float(sqrt(H[0]**2+H[1]**2))))
    s = []
    for x in chain_rings:
        d = sqrt((x[0]-H[0])**2 + (x[1]-H[1])**2)
        s.append(acos(min(mpf(1), d/(2*R))))
    cap = s[0] + s[-1] + 2*sum(s[1:-1])
    th = []
    for i in range(m):
        a, b = chain_rings[i], chain_rings[i+1]
        v1 = (a[0]-H[0], a[1]-H[1]); v2 = (b[0]-H[0], b[1]-H[1])
        n1 = sqrt(v1[0]**2+v1[1]**2); n2 = sqrt(v2[0]**2+v2[1]**2)
        th.append(acos(max(mpf(-1), min(mpf(1), (v1[0]*v2[0]+v1[1]*v2[1])/(n1*n2)))))
    P("   turn span Theta = %.12f ; transfer cap s_1+s_6+2*sum(int) = %.12f ; slack = %.3e"
      % (float(sum(th)), float(cap), float(cap - sum(th))))
    P("   interior spokes s_2..s_5 = %s" % [round(float(x), 6) for x in s[1:-1]])
    P("   => (E2) interior content = sum_interior s_i = %.12f ; endpoint part = %.12f"
      % (float(sum(s[1:-1])), float(s[0]+s[-1])))

    P("")
    P("C. COUNTEREXAMPLE ATTACK on the naivety '(E1) is a ring-only identity for any legal chain'")
    P("   build a legal 3-ring chain (one hub serves both edges) whose three arcs are DISJOINT, hence")
    P("   the covered measure is a SUM of arcs and (E1)'s endpoint formula is false without contiguity.")
    rm = mpf('0.38')
    hub = (mpf('0.149'), mpf(0))          # small |hub|, as at the record object
    rad = mpf('0.70')                     # ring radius inside [1-r, 1] = [0.62, 1]
    angs1 = [mpf(-1.0472), mpf(0), mpf(1.0472)]   # -60, 0, +60 deg (adjacent gap 60 deg < 65.8 deg)
    rings3 = [(rad*mp.cos(a), rad*mp.sin(a)) for a in angs1]
    A, M, B = rings3
    P("   hub = (%.3f,0), r = %.3f ; |A|=|M|=|B| = %.3f in [1-r,1]=[%.3f,1] ; hub-azimuths -60,0,+60 deg"
      % (hub[0], rm, rad, 1-rm))
    pinAM = pin_of(A, M, rm); pinMB = pin_of(M, B, rm)
    if pinAM is not None and pinMB is not None:
        def dist(p, q):
            return sqrt((p[0]-q[0])**2 + (p[1]-q[1])**2)
        P("   pins exist (adjacent ring distance %.3f <= 2r = %.3f)"
          % (float(sqrt((A[0]-M[0])**2+(A[1]-M[1])**2)), float(2*rm)))
        P("   pin(A,M) hub-distance - r = %+.3e ; pin(M,B) hub-distance - r = %+.3e"
          % (float(dist(pinAM, hub) - rm), float(dist(pinMB, hub) - rm)))
        ws = [float(u_arc(x, rm)*180/MP_PI) for x in rings3]
        azs = [atan2(x[1], x[0]) for x in rings3]
        P("   arcs half-widths (deg) = %s ; azimuths (deg) = %s"
          % ([round(w, 3) for w in ws], [round(float(a*180/MP_PI), 3) for a in azs]))
        gaps = []
        for i in range(2):
            d = azs[i+1]-azs[i]
            gaps.append(float((d if d > 0 else d + 2*MP_PI)*180/MP_PI))
        P("   azimuth gaps between neighbouring arcs (deg) = %s ; arc widths (deg) = %s"
          % ([round(g, 3) for g in gaps], [round(2*w, 3) for w in ws]))
        P("   arc 1 ends at %.3f deg, arc 2 starts at %.3f deg -> GAP %.3f deg > 0: arcs DISJOINT"
          % (float(azs[0]*180/MP_PI) + ws[0], float(azs[1]*180/MP_PI) - ws[1],
             float((azs[1]*180/MP_PI) - ws[1]) - (float(azs[0]*180/MP_PI) + ws[0])))
        P("   endpoints' own span = 2*beta_1 = %.3f deg, while the covered measure is the SUM of three"
          % (2*ws[0]))
        P("   arcs = %.3f deg (three disjoint pieces) — so (E1) is NOT an identity for arbitrary legal"
          % (sum(2*w for w in ws)))
        P("   chains; contiguity is an extra hypothesis that the boundary-COVER requirement supplies.")
    P("")
    P("D. SCOPE: formulation + instantiation + one attack, as budgeted.  (E1) is an identity under")
    P("   contiguity (interior rings cancel exactly); (E2) is the interior-dependent functional whose")
    P("   DP reduces to maximising sum_interior s_i subject to K != empty, with the extremal")
    P("   configuration characterised by MEC(pins) = r (all pins on the hub circle) by compactness +")
    P("   monotonicity.  No numeric value here is claimed exact; no tightness normal form is assumed.")

    (OUT / "r20_chain_extent_oc.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_chain_extent_oc.txt"))


if __name__ == "__main__":
    main()
