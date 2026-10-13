"""r20-chain: THE CORNER-CAPACITY SUM, exact and decisive.

Setting (established q0 two-hub class): unit disk D covered by 11 congruent radius-R disks,
nine essential ring disks + two interior hubs A,B.  Each ring edge is realised by at least
one hub; call it SERVED by that hub.  The served edges of one hub form a contiguous arc of
the 9-cycle, and the two arcs partition the cycle.

FACT (circumradius criterion).  Face (H,c_i,c_{i+1}) has circumradius <= R iff
      theta_i^H  <=  s_H(c_i) + s_H(c_{i+1}),      s_H(c) = arccos(|H-c|/(2R)),
defined only when both |H-c| <= 2R.

FACT (ring arithmetic / corollary).  Let the two shared CORNERS of the partition be the
two ring vertices where the served arcs change hands.  The two hubs provide ALL the
turning at those corners, so
      (sum of the two corner caps)
        := (s_A(y)+s_A(x)) + (s_B(y)+s_B(x))   >=   2*pi ,
where x,y are the two corner ring vertices.  (Coarser but related: for each hub the sum of
the caps of the edges it serves is >= 2pi.)

This file measures, at the candidate, the corner caps, and then tests by global random
search whether the corner-cap inequality can fail.
"""
import json, numpy as np
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
OBJ = HERE.parent.parent / "cline2-sharp-fan" / "out" / "certified_object_copy.json"
log = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); log.append(s)

obj = json.loads(OBJ.read_text(encoding="utf-8"))
C = np.array([[int(a) / 1e17, int(b) / 1e17] for a, b in obj["centers_scaled_1e17"]])
Rc = float(obj["certified_interval"]["lo"])
HA, HB = C[0], C[2]
ID = np.array([1, 3, 4, 5, 6, 7, 8, 9, 10])
ring0 = C[ID]
ord0 = np.argsort(np.arctan2(ring0[:, 1], ring0[:, 0]))
ring0 = ring0[ord0]; ID0 = ID[ord0]
P("ring sites in polar order:", list(ID0))
def s_of(H, c, R):
    d = np.linalg.norm(np.asarray(c) - H)
    return np.arccos(np.clip(d / (2 * R), -1, 1)) if d <= 2 * R else np.inf

P("\n=== corner caps at the certified candidate ===")
for R in (Rc, 0.38):
    P(f"\n  R = {R:.17f}")
    for i, c in enumerate(ring0):
        sa, sb = s_of(HA, c, R), s_of(HB, c, R)
        P(f"    ring {ID0[i]:>2d}: |A-c|={np.linalg.norm(c-HA):.6f} |B-c|={np.linalg.norm(c-HB):.6f}"
          f"   s_A={sa:.6f} {'(inf)' if not np.isfinite(sa) else ''}   s_B={sb:.6f} {'(inf)' if not np.isfinite(sb) else ''}")
    # candidate corner pair: 3 and 4 (the shared endpoints of the two chains)
    for (x, y) in [(3, 4)]:
        ix, iy = list(ID0).index(x), list(ID0).index(y)
        capsum = s_of(HA, ring0[ix], R) + s_of(HA, ring0[iy], R) + \
                 s_of(HB, ring0[ix], R) + s_of(HB, ring0[iy], R)
        P(f"    corner caps at ({x},{y}):  {capsum:.10f}   minus 2pi = {capsum-2*np.pi:+.6f}")
    # all nine (x,y) pairs of (possibly non-adjacent) corner vertices
    n = len(ID0)
    best = -1e9
    for a in range(n):
        for b in range(a + 1, n):
            cps = s_of(HA, ring0[a], R) + s_of(HA, ring0[b], R) + \
                  s_of(HB, ring0[a], R) + s_of(HB, ring0[b], R)
            if np.isfinite(cps) and cps > best:
                best = cps
    P(f"    best (largest) corner-cap sum over all vertex pairs = {best:.6f}")
    worst = 1e9
    for a in range(n):
        for b in range(a + 1, n):
            cps = s_of(HA, ring0[a], R) + s_of(HA, ring0[b], R) + \
                  s_of(HB, ring0[a], R) + s_of(HB, ring0[b], R)
            if np.isfinite(cps) and cps < worst:
                worst = cps
    P(f"    smallest corner-cap sum over all vertex pairs = {worst:.6f}")

P("\n=== is the corner-cap inequality >= 2pi automatic?  randomised test ===")
rng = np.random.default_rng(7)
worst = 1e9; worst_case = None
for trial in range(200000):
    R = 0.38
    hA = rng.uniform(-1, 1, 2) * (1 - R); hB = rng.uniform(-1, 1, 2) * (1 - R)
    # nine ring sites: uniform in the annulus 1-R <= |c| <= 1
    th = rng.uniform(0, 2 * np.pi, 9); rho = np.sqrt(rng.uniform((1 - R) ** 2, 1.0, 9))
    ring = np.stack([rho * np.cos(th), rho * np.sin(th)], 1)
    o = np.argsort(np.arctan2(ring[:, 1], ring[:, 0])); ring = ring[o]
    for a in (0, 1):
        for b in range(a + 1, 9):
            cps = s_of(hA, ring[a], R) + s_of(hA, ring[b], R) + \
                  s_of(hB, ring[a], R) + s_of(hB, ring[b], R)
            if np.isfinite(cps) and cps < worst:
                worst, worst_case = cps, (R, hA.copy(), hB.copy(), ring.copy(), a, b)
P(f"  smallest corner-cap sum found over 200000 random legal-looking configurations: {worst:.6f}")
P(f"  (2pi = {2*np.pi:.6f})   inequality corner caps >= 2pi is {'SUPPORTED' if worst>=2*np.pi else 'REFUTED'}")

P("\n=== the two-hub TOTAL cap sum at the candidate and the exclusion question ===")
tot = sum(s_of(HA, c, Rc) + s_of(HB, c, Rc) for c in ring0)
P(f"  sum over all nine ring sites of (s_A + s_B) = {tot:.10f}   minus 2pi = {tot-2*np.pi:+.6f}")
P("  (note: (s_A+s_B)(x) + (s_A+s_B)(y) = 2*s_corner; the corner sum is HALF of this for a pair)")

(OUT / "corner_capacity.txt").write_text("\n".join(log) + "\n")
P("\nwrote " + str(OUT / "corner_capacity.txt"))
