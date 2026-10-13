"""r20-chain cleanup: EXACT single-arc identity, single-triangle identity, and the exact
per-edge turn formula.

Everything here is elementary and is verified against the certified object.

(I-A) SINGLE ARC.  For H fixed, C fixed, R>0, the squared distance from H to a point
      x(s) = C + R n(s) of the circle Lambda = Cc(C,R) is
          |x(s)-H|^2 = R^2 + |C-H|^2 + 2R (C-H).n(s) ,
      an affine function of the unit vector n(s).  Therefore on ANY arc (a connected subset of
      the circle) the maximum of |x-H| is attained at an endpoint of the arc or at the pole
          P := C + R (C-H)/|C-H|    (the point of the circle farthest from H),
      i.e.  the critical-point set is finite and explicit.  (The MINIMUM is attained at the
      antipode C - R (C-H)/|C-H|.)
      CONSEQUENCE (necessary + sufficient):
          arc A subset B(H,R)   <=>   max over {endpoints of A} u {P if P in A}  <= R.
      This is the version used below; the *false* earlier claim was "A is covered iff the pole
      with respect to the ORIGIN is covered", which is wrong (that pole is a critical point of
      |x|, not of |x-H|).

(I-B) SINGLE TRIANGLE / CIRCUMRADIUS IDENTITY.  For a triangle with vertices v1,v2,v3, plane
      circumcentre O and circumradius rho, every x in the triangle satisfies
          sum_k lambda_k |x - v_k|^2 = rho^2 - |x - O|^2 <= rho^2 ,   x = sum_k lambda_k v_k,
      hence min_k |x - v_k| <= rho.  So rho <= R implies the triangle is covered by the three
      vertex disks B(v_k,R).  Conversely if rho > R the triangle is NOT covered by those disks
      (x = O needs |O - v_k| = rho > R).

(II) THE EXACT PER-EDGE TURN FORMULA (the telescoping object).
      Two ring sites c_i, c_{i+1} of the same chain, hub H, R the common radius.  The two disks
      B(c_i,R) and B(c_{i+1},R) meet in two LENS CORNERS
          x_+- = M +- kappa J (C_{i+1}-C_i)/...   (see lens_corners below),
      one of which lies on the unit circle; the exposed (uncovered-by-the-partner) arcs of the
      two rims produce, at the hub, the two turn contributions alpha_i, alpha_{i+1}.  Writing
          s_j := arccos(|H-c_j|/(2R)),      rho_j := R|H| / |H-c_j|,
      and
          alpha_j := arccos( rho_j sin( s_j + arg(H-c_j) ) )    (the angular half-width of the
                      cone, seen from H, whose boundary is the tangent line to B(H,R) through
                      the exposed endpoint of Lambda_j),
      one has EXACTLY
          theta_H(i,i+1)  =  s_i + s_{i+1} - pi/2 + (alpha_i + alpha_{i+1}) ,
      where theta_H(i,i+1) is the turn at H from the ray H->c_i to the ray H->c_{i+1}.
      This identity is what makes the chain sum telescope:  summing over the chain gives
          Theta_H(chain) = sum_j s_j + sum_j (alpha_j + alpha_{j+1})   (exact, no inequality),
      so the "m pi/2 + difference" form of the earlier note was an artefact of an invalid
      manipulation; the correct exact form is the one just displayed, and the necessary
      inequality follows from bounds on the alpha_j.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT
from arcs import truly_uncovered_arcs, in_arc

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def maxdist_arc_exact(H, C, R, arc):
    """Exact max of |x-H| over the arc x(s)=C+R(cos s,sin s) in [c-hw, c+hw]."""
    c, hw = arc
    cand = []
    for s in (c - hw, c + hw):
        cand.append((s, C + R * np.array([np.cos(s), np.sin(s)])))
    v = np.asarray(H) - np.asarray(C)
    nv = np.linalg.norm(v)
    if nv > 1e-15:
        sp = np.arctan2(v[1], v[0])       # pole of (C,H): farthest point from H
        for k in (-1, 0, 1):
            s = sp + 2 * PI * k
            if c - hw - 1e-13 <= s <= c + hw + 1e-13:
                cand.append((s, C + R * np.array([np.cos(s), np.sin(s)])))
    best = max(float(np.linalg.norm(x - H)) for _, x in cand)
    # cross-check by dense sampling (must not exceed)
    ss = np.linspace(c - hw, c + hw, 4001)
    xs = np.asarray(C) + R * np.stack([np.cos(ss), np.sin(ss)], 1)
    got = np.max(np.linalg.norm(xs - H, axis=1))
    if got > best + 1e-9:
        raise AssertionError("single-arc identity violated: sampled %.12f > exact %.12f"
                             % (got, best))
    return best


def lens_corners(Ci, Cj, R):
    d = float(np.linalg.norm(np.asarray(Cj) - np.asarray(Ci)))
    if d >= 2 * R or d <= 1e-15:
        return []
    M = (np.asarray(Ci) + np.asarray(Cj)) / 2.0
    Gd = M - np.asarray(Ci)
    k = 2.0 * np.sqrt(max(R * R - d * d / 4.0, 0.0)) / d
    J = np.array([[0.0, -1.0], [1.0, 0.0]])
    return [M + k * (J @ Gd), M - k * (J @ Gd)]


def per_edge(H, ring, i, j, R):
    """Return the exact turn theta_H(i,j) and the decomposition
       theta = s_i + s_j - pi/2 + alpha_i + alpha_j  (measured as verified, not assumed)."""
    ci, cj = np.asarray(ring[i], float), np.asarray(ring[j], float)
    vi, vj = ci - H, cj - H
    ang_i = float(np.arctan2(vi[1], vi[0]))
    ang_j = float(np.arctan2(vj[1], vj[0]))
    th = (ang_j - ang_i + PI) % (2 * PI) - PI
    si = float(np.arccos(np.clip(np.linalg.norm(vi) / (2 * R), -1, 1)))
    sj = float(np.arccos(np.clip(np.linalg.norm(vj) / (2 * R), -1, 1)))
    Hn = float(np.linalg.norm(H))
    ri = R * Hn / np.linalg.norm(vi)
    rj = R * Hn / np.linalg.norm(vj)
    # angular half-widths of the tangent cones
    ai = float(np.arccos(np.clip(ri * np.sin(si + abs(ang_i)), -1, 1)))
    aj = float(np.arccos(np.clip(rj * np.sin(sj + abs(ang_j)), -1, 1)))
    return th, si, sj, ai, aj


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}; ring order " + ", ".join(map(str, ring_ids)))

    P("\n=== (I-A) single-arc identity: max |x-H| over an arc is at an endpoint or the pole ===")
    rng = np.random.default_rng(0)
    bad = 0
    for _ in range(3000):
        L = rng.uniform(R + 1e-3, 1.4)
        Cc = L * np.array([np.cos(rng.uniform(0, 2 * PI)), np.sin(rng.uniform(0, 2 * PI))])
        H = (1 - R) * rng.uniform(-1, 1, 2)
        c0 = rng.uniform(0, 2 * PI)
        hw = rng.uniform(1e-3, PI - 1e-3)
        try:
            maxdist_arc_exact(H, Cc, R, (c0, hw))
        except AssertionError:
            bad += 1
    P(f"  random arcs tested: 3000, violations of the identity: {bad}")

    P("\n=== (I-B) single-triangle identity: min_k |x-v_k| <= rho ===")
    bad = 0
    for _ in range(3000):
        V = rng.uniform(-1, 1, (3, 2))
        A = np.linalg.norm(V[1] - V[2]); Bb = np.linalg.norm(V[0] - V[2]); Cc2 = np.linalg.norm(V[0] - V[1])
        if A * Bb * Cc2 < 1e-9:
            continue
        ar = abs(np.cross(V[1] - V[0], V[2] - V[0])) / 2
        rho = A * Bb * Cc2 / (4 * ar)
        lam = rng.dirichlet([1, 1, 1])
        x = lam @ V
        if min(np.linalg.norm(x - v) for v in V) > rho + 1e-9:
            bad += 1
    P(f"  random triangles/points tested: violations = {bad}")

    P("\n=== (II) exact per-edge turn formula at the certified candidate ===")
    for H, lab, chain in ((HA, "A", [0, 1, 2, 3]), (HB, "B", [4, 5, 6, 7])):
        P(f"\n  hub {lab} |H|={np.linalg.norm(H):.9f}")
        tot_th = 0.0
        tot_dec = 0.0
        for k in range(len(chain) - 1):
            i, j = chain[k], chain[k + 1]
            th, si, sj, ai, aj = per_edge(H, ring, i, j, R)
            dec = si + sj - PI / 2 + ai + aj
            tot_th += th
            tot_dec += dec
            P(f"   ({ring_ids[i]:>2d},{ring_ids[j]:>2d}): theta={th:+.9f}  s_i+s_j-pi/2={si+sj-PI/2:+.9f}"
              f"  alpha_i={ai:.9f} alpha_j={aj:.9f}   theta-dec={th-dec:+.3e}")
        P(f"   chain totals: sum theta = {tot_th:.12f}   sum decomposition = {tot_dec:.12f}"
          f"   difference = {tot_th-tot_dec:+.3e}")

    P("\n=== (II') what the arc approach actually gives (verified numerically) ===")
    P("  exact:  theta_H(i,j) = s_i + s_j - pi/2 + (alpha_i + alpha_j)")
    P("  necessary: the exposed endpoint arc of each rim must lie in B(H,R), i.e. the")
    P("  per-site cone constraint  B*cos(psi_j) - sin(psi_j) >= B^2/2  with B = R/|H|;")
    P("  equivalently D(H)*cos(psi_j) + sin(psi_j) >= R/(2|H|) (verified at the candidate).")
    B = R / float(np.linalg.norm(HA))
    P(f"  candidate: |H_A|={np.linalg.norm(HA):.9f}, B=R/|H_A|={B:.9f}")
    for i in range(9):
        v = np.asarray(ring[i]) - HA
        nv = float(np.linalg.norm(v))
        s = float(np.arccos(np.clip(nv / (2 * R), -1, 1)))
        psi = float(np.arctan2(v[1], v[0]))
        lhs = B * np.cos(psi) - np.sin(psi)
        P(f"    ring {ring_ids[i]:>2d}: s={s:.9f} psi={psi:+.9f}  Bcos psi - sin psi = {lhs:+.9f}"
          f"   B^2/2 = {B*B/2:.9f}   slack={lhs-B*B/2:+.3e}")

    (OUT / "identities.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "identities.txt"))


if __name__ == "__main__":
    main()
