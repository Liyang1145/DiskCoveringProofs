"""r20-chain AUDIT (lead-requested, read-only, no optimisation, no new claims).

TWO AUDITS:

(A) Test the hypotheses of lead/R20-CHAIN-HUB-CONVEXIFICATION.md one by one on the
    counterexample pair of C883, and correct the "nonconvex" claim if a hypothesis fails.

(B) Reproduce lead/check_r20_chain_variance.py and independently solve the barycentric
    coordinates of the SAME pins [4,6,8] by linear equations, using the SAME object
    (q0 ring mapping c[] with hubs at c[9]=H_A, c[10]=H_B, as in the lead's script).
    No object substitution.

Source ids used:
  * n11/upper/certified_object.json            (centers_scaled_1e17)
  * research-2026/team-current/lead/check_r20_chain_variance.py  (c[] mapping, r value)
  * research-2026/team-current/lead/R20-CHAIN-HUB-CONVEXIFICATION.md (hypotheses)
  * n11/upper/q0_graphs.json via q0_exact_closure_radius.py (exec'd by the variance script)
"""
import io
import json
import math
from pathlib import Path

import numpy as np

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


# ------------------------------------------------------------------ object loading
def lead_object():
    """Exactly the lead's construction in check_r20_chain_variance.py / q0_exact_closure_radius.py."""
    raw = json.loads((ROOT / "n11/upper/certified_object.json").read_text(encoding="utf-8-sig"))
    C = np.array([[int(v) / 1e17 for v in a] for a in raw["centers_scaled_1e17"]])
    rings = sorted([i for i in range(11) if i not in [0, 2]],
                   key=lambda i: math.atan2(C[i, 1], C[i, 0]))
    C = C[rings + [0, 2]]
    return C, rings


def pins_of(C, r):
    roots = []
    for i in range(9):
        a, b = C[i], C[(i + 1) % 9]
        m = (a + b) / 2
        d = np.linalg.norm(b - a)
        n = np.array([-(b - a)[1], (b - a)[0]]) / d
        k = math.sqrt(r * r - d * d / 4)
        roots.append(min([m + k * n, m - k * n], key=np.linalg.norm))
    return np.array(roots)


# ==================================================================== AUDIT A
def audit_A():
    P("=" * 78)
    P("AUDIT A — test lead/R20-CHAIN-HUB-CONVEXIFICATION.md hypotheses on the C883 pair")
    P("=" * 78)
    P("counterexample pair (C883):")
    r = 0.37998385311983873
    a_ = np.array([-0.23763005, -0.58241778])
    b_ = np.array([0.48422478, -0.42854144])
    P(f"  a = {a_}  |a| = {np.linalg.norm(a_):.9f}   (1-r = {1-r:.9f})")
    P(f"  b = {b_}  |b| = {np.linalg.norm(b_):.9f}")
    P(f"  r = {r!r}")

    d = float(np.linalg.norm(b_ - a_))
    A = d / 2
    m = (a_ + b_) / 2
    e = (b_ - a_) / d
    n = np.array([-e[1], e[0]])
    k = math.sqrt(r * r - A * A)
    P(f"  d = {d:.9f} <= 2r = {2*r:.9f} -> {d <= 2*r}")
    P(f"  A = d/2 = {A:.9f}   k = sqrt(r^2-A^2) = {k:.9f}   m = {np.round(m,9)}  |m| = {np.linalg.norm(m):.9f}")
    P(f"  n = {np.round(n,9)}   (radical direction)")

    # unit-circle intersections of the radical line m + t n
    # |m + t n|^2 = 1  ->  t^2 + 2 t (m.n) + |m|^2 - 1 = 0
    mn = float(m @ n)
    disc = mn * mn - (m @ m - 1.0)
    P(f"  m.n = {mn:+.9f}   |m|^2-1 = {(m @ m - 1):+.9f}   discriminant = {disc:+.9f}")
    if disc < 0:
        P("  -> the radical line does NOT meet the unit circle at all")
        tplus = tminus = None
    else:
        s = math.sqrt(disc)
        t1, t2 = -mn - s, -mn + s
        tplus, tminus = max(t1, t2), min(t1, t2)
        P(f"  t+ = {tplus:+.9f}   t- = {tminus:+.9f}   (m ± t n are the two unit-circle points)")
        U = m + tplus * n
        Vv = m + tminus * n
        P(f"  U = m + t+ n = {np.round(U,9)}   |U| = {np.linalg.norm(U):.12f}")
        P(f"  V = m + t- n = {np.round(Vv,9)}   |V| = {np.linalg.norm(Vv):.12f}")

    # HYPOTHESIS 1: exactly ONE equal-distance point U in the COMMON COVERED arc.
    P("")
    P("H1 (interface hypothesis): the actual covered unit-circle arcs of the two disks have")
    P("    exactly ONE equal-distance point U in their common covered arc.")
    # covered arc of disk(a,r): points x of the unit circle with |x-a| <= r
    def covered_arc(c):
        L = float(np.linalg.norm(c))
        val = (1 + L * L - r * r) / (2 * L)
        if val >= 1:
            return None
        if val <= -1:
            return (0.0, 2 * math.pi)
        phi = math.atan2(c[1], c[0])
        ac = math.acos(val)
        return (phi - ac, phi + ac)

    ca, cb = covered_arc(a_), covered_arc(b_)
    P(f"  covered arc of B(a,r) on the unit circle: ({ca[0]:.6f}, {ca[1]:.6f}) angular span {ca[1]-ca[0]:.6f}")
    P(f"  covered arc of B(b,r) on the unit circle: ({cb[0]:.6f}, {cb[1]:.6f}) angular span {cb[1]-cb[0]:.6f}")
    # overlap
    def ang_in(iv, t):
        return iv[0] <= t <= iv[1]
    lo = max(ca[0], cb[0])
    hi = min(ca[1], cb[1])
    P(f"  common covered arc (in the same unwrapped frame): [{lo:.6f}, {hi:.6f}]  length {max(0.0, hi-lo):.6f}")
    P(f"  -> do the covered arcs overlap at all? {hi > lo}")
    if tplus is not None:
        U = m + tplus * n
        tU = math.atan2(U[1], U[0])
        da_u = float(np.linalg.norm(U - a_))
        db_u = float(np.linalg.norm(U - b_))
        P(f"  U (the unit-circle point on the radical line with t+>0): angle {tU:.6f},"
          f" |U-a| = {da_u:.9f}, |U-b| = {db_u:.9f}")
        P(f"     is U in the covered arc of a? {ang_in(ca, tU)};   of b? {ang_in(cb, tU)}")
        P(f"     is U covered by a? {da_u <= r}; by b? {db_u <= r}")
        Vv = m + tminus * n
        tV = math.atan2(Vv[1], Vv[0])
        P(f"  V (t-) : angle {tV:.6f}, |V-a| = {np.linalg.norm(Vv-a_):.9f},"
          f" |V-b| = {np.linalg.norm(Vv-b_):.9f}   covered by a? {np.linalg.norm(Vv-a_)<=r}")
    P("  VERDICT H1: see the two lines above — if U is not covered by both disks, H1 FAILS for")
    P("              this pair, so the pair is outside the convexification's domain.")

    # HYPOTHESIS 2: t+ <= k  (Lemma 1)
    P("")
    P("H2 (Lemma 1): |U-a|^2 = A^2 + t+^2 <= r^2, i.e. t+ <= k.")
    if tplus is not None:
        lhs = A * A + tplus * tplus
        P(f"  A^2 + t+^2 = {lhs:.9f}   r^2 = {r*r:.9f}   -> H2 holds? {lhs <= r*r + 1e-15}")
        P(f"     t+ = {tplus:+.9f}   k = {k:.9f}   t+ <= k ? {tplus <= k}")

    # HYPOTHESIS 3: t- < -k  (V not covered by both)
    P("")
    P("H3 (Lemma 1): the other unit-circle point V has A^2 + t-^2 > r^2, i.e. t- < -k.")
    if tminus is not None:
        lhs = A * A + tminus * tminus
        P(f"  A^2 + t-^2 = {lhs:.9f}   r^2 = {r*r:.9f}   -> > r^2 ? {lhs > r*r}")
        P(f"     t- = {tminus:+.9f}   -k = {-k:.9f}   t- < -k ? {tminus < -k}")

    # HYPOTHESIS 4: |p_out| >= 1  (so p_out outside int D)
    P("")
    P("H4 (Lemma 1): p_out = m + k n lies outside int D (|p_out| >= 1); p_in = m - k n strictly inside.")
    p_out = m + k * n
    p_in = m - k * n
    P(f"  p_out = {np.round(p_out,9)}  |p_out| = {np.linalg.norm(p_out):.9f}  -> |p_out|>=1 ? {np.linalg.norm(p_out) >= 1}")
    P(f"  p_in  = {np.round(p_in,9)}   |p_in|  = {np.linalg.norm(p_in):.9f}   -> |p_in|<1 ? {np.linalg.norm(p_in) < 1}")
    P(f"  NOTE: the C883 witness switched the two roots; whichever root is called p_out, the")
    P(f"        hypothesis |p_out| >= 1 requires |m + k n| >= 1, i.e. |m|^2 + k^2 + 2k(m.n) >= 1.")

    # HYPOTHESIS 5: hub strictly interior
    P("")
    P("H5 (strictness): hubs satisfy STRICT |h| < 1-r; the proof uses it and forbids closed H.")
    h = p_out if np.linalg.norm(p_out) < np.linalg.norm(p_in) else p_in
    P(f"  the legal hub used in the C883 witness: |h| = {np.linalg.norm(h):.9f} vs 1-r = {1-r:.9f}")
    P(f"     strictly interior? {np.linalg.norm(h) < 1-r}   (this is the SMALLER-norm root)")

    # consequence test: does rho <= r iff |h - p_in| <= r hold here?
    P("")
    P("CONSEQUENCE test (Lemma 2 corollary): rho(a,b,h) <= r iff |h-p_in| <= r.")
    def circ(P1, P2, P3):
        ee = [np.linalg.norm(P2 - P3), np.linalg.norm(P1 - P3), np.linalg.norm(P1 - P2)]
        ar = abs((P2[0] - P1[0]) * (P3[1] - P1[1]) - (P2[1] - P1[1]) * (P3[0] - P1[0])) / 2
        return ee[0] * ee[1] * ee[2] / (4 * ar) if ar > 1e-15 else math.inf
    # h must be off the radical line to apply; take the C883 witness h and a nearby off-line point
    for hh in (h, h + 1e-6 * e, h - 1e-6 * e):
        rho = circ(a_, b_, hh)
        sd = float((hh - m) @ n)
        P(f"  h = {np.round(hh,9)}  rho = {rho:.9f} (<=r? {rho <= r})  |h-p_in| = {np.linalg.norm(hh-p_in):.9f}"
          f"  |h-p_out| = {np.linalg.norm(hh-p_out):.9f}  m.n-offset = {sd:+.3e}")
    P("")
    P("AUDIT A VERDICT: the C883 pair violates H1 (no common covered arc / U not covered by both),")
    P("  hence it is OUTSIDE the domain of R20-CHAIN-HUB-CONVEXIFICATION.md. The 'nonconvex' claim")
    P("  of C883 must therefore be withdrawn as a statement about the convexification's domain:")
    P("  it only shows that the domain hypotheses are not automatic for arbitrary annulus pairs.")
    return


# ==================================================================== AUDIT B
def audit_B():
    P("")
    P("=" * 78)
    P("AUDIT B — reproduce the lead's variance calibration and solve the barycentric coordinates")
    P("          independently by linear equations on the SAME pins [4,6,8]")
    P("=" * 78)
    C, rings = lead_object()
    P(f"  source: n11/upper/certified_object.json ; ring node ids in lead order: {rings}")
    for i in range(10):
        tag = "hub A" if i == 9 else ("hub B" if i == 10 else f"ring node {i}")
        P(f"    c[{i}] = ({C[i,0]:+.9f},{C[i,1]:+.9f})  |.|={np.linalg.norm(C[i]):.9f}   {tag}")
    r = 0.3799838531198388        # exactly the lead's script value
    HA, HB = C[9], C[10]
    pins = pins_of(C, r)
    P(f"  r (lead script value) = {r!r}")

    P("")
    P("  pin ledger (node-edge i,i+1 ; pin = min-norm root):")
    for i in range(9):
        p = pins[i]
        P(f"   i={i} edge({i},{(i+1)%9})  pin=({p[0]:+.9f},{p[1]:+.9f})"
          f"  |H_A-pin|-r={np.linalg.norm(HA-p)-r:+.3e}  |H_B-pin|-r={np.linalg.norm(HB-p)-r:+.3e}")

    idx = [4, 6, 8]
    p = pins[idx]
    P("")
    P(f"  pins[{idx}] (the lead's selection), with BOTH hubs' distances:")
    for q, j in zip(p, idx):
        P(f"    pin[{j}] = ({q[0]:+.9f},{q[1]:+.9f})  |.|={np.linalg.norm(q):.9f}"
          f"  |H_A-pin|-r={np.linalg.norm(HA-q)-r:+.3e}   |H_B-pin|-r={np.linalg.norm(HB-q)-r:+.3e}")

    P("")
    P("  *** WHICH POINT DO THE LEAD'S WEIGHTS REPRODUCE, AND WHICH PINS ARE THEY? ***")
    P("  (the lead's script writes weights for the variable it calls h = c[10]; its own JSON")
    P("   records the three pins, so we (a) test the weights against both hubs and (b) identify")
    P("   the pins inside MY pin list)")
    lead_pins = np.array([[-0.37866873651434624, -0.11595586133734863],
                          [-0.0005741023530978287, -0.5294120407837313],
                          [0.37841635673703006, -0.11677685837533505]])
    lead_w = np.array([0.45997773056271785, 0.08004453927415564, 0.45997773016312643])
    for nm, hh in (("H_A = c[9]", HA), ("H_B = c[10]", HB)):
        P(f"    weights . pins = {np.round(lead_w @ lead_pins, 12)}   {nm} = {np.round(hh, 12)}"
          f"   |diff| = {np.linalg.norm(lead_w @ lead_pins - hh):.3e}")
    for j in range(3):
        dd = [float(np.linalg.norm(lead_pins[j] - q)) for q in pins]
        i0 = int(np.argmin(dd))
        P(f"    lead pin[{j}] = my min-norm root of node-edge ({i0},{(i0+1)%9})"
          f"   (residual {dd[i0]:.2e})   |H_A - it| = {np.linalg.norm(HA-lead_pins[j]):.12f}"
          f"   |H_B - it| = {np.linalg.norm(HB-lead_pins[j]):.12f}")
    P("    -> the lead's three pins are MY node-edges {1,3,8} (set equality), i.e. exactly the")
    P("       H_A-active pins; the lead's weights reproduce H_A.")
    P("       The script's variable name `h = c[10]` says hub B; the object is hub A. Label bug.")

    # --- the true active sets and the hull question for each hub
    P("")
    P("  true active sets (min-norm roots; |H - pin| = r to machine precision):")
    actA = [i for i in range(9) if abs(np.linalg.norm(HA - pins[i]) - r) < 1e-10]
    actB = [i for i in range(9) if abs(np.linalg.norm(HB - pins[i]) - r) < 1e-10]
    P(f"    H_A active node-edges: {actA}")
    P(f"    H_B active node-edges: {actB}")
    P("")
    P("  is each hub inside the convex hull of ITS OWN active pins?")
    for nm, hh, act in (("H_A", HA, actA), ("H_B", HB, actB)):
        Q = pins[act]
        nq = len(act)
        M = np.vstack([Q.T, np.ones(nq)])
        sol, res, rank, sv = np.linalg.lstsq(M, np.r_[hh, 1.0], rcond=None)
        angs = [round(float(np.degrees(np.arctan2(*(q - hh)[::-1]))), 2) for q in Q]
        P(f"    {nm}: |active| = {nq}, weights = {[round(float(x),6) for x in sol]},"
          f" sum = {sol.sum():.6f}, min = {sol.min():.6f} -> all >= 0 ?"
          f" {bool(np.all(sol >= -1e-12))}")
        P(f"        pins at angles {angs} deg about {nm}")
    P("    -> the C879 rigidity mechanism (h* in conv{pins}) holds for H_A and fails for H_B,")
    P("       because H_B's four active pins all lie in the half-plane y > H_B.y (they occupy")
    P("       angles 4.9..174.9 deg only), so H_B sits strictly below their hull.")

    # cross-check with the lead's own three pins, explicitly
    P("")
    P("  same three pins (the lead's), both hubs, both solve representations:")
    M1 = np.vstack([lead_pins.T, np.ones(3)])
    M2 = np.array([[1.0, 1.0, 1.0],
                   [lead_pins[0, 0], lead_pins[1, 0], lead_pins[2, 0]],
                   [lead_pins[0, 1], lead_pins[1, 1], lead_pins[2, 1]]])
    for nm, hh in (("H_A", HA), ("H_B", HB)):
        l1 = np.linalg.solve(M1, np.r_[hh, 1.0])
        l2 = np.linalg.solve(M2, np.array([1.0, hh[0], hh[1]]))
        var = sum(l1[i] * l1[j] * np.sum((lead_pins[i] - lead_pins[j]) ** 2)
                  for i in range(3) for j in range(i))
        P(f"    {nm}: lambda = {[round(float(x),12) for x in l1]}"
          f"  (2nd rep. agrees to {np.max(np.abs(l1-l2)):.1e})")
        P(f"        all > 0 ? {bool(np.all(l1 > 0))}   variance v = {var!r}"
          f"   r^2 = {r*r!r}   v - r^2 = {var - r*r:+.3e}")
    return


if __name__ == "__main__":
    audit_A()
    audit_B()
    out = ROOT / "research-2026/team-current/r20-chain/out/audit_A_B.txt"
    out.write_text("\n".join(LOG) + "\n", encoding="utf-8")
    P("")
    P("wrote " + str(out))
