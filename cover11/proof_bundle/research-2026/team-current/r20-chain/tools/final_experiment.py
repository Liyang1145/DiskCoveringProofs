"""r20-chain FINAL EXPERIMENT: the cluster-capacity bound for the q0(6,7) two-hub class.

SETUP (all established reductions, no symmetry/equality assumptions):
  unit closed disk D; 11 congruent disks of radius R cover D; nine essential boundary
  ("ring") disks + two strictly interior hubs A,B.  Ring sites c_0..c_8 ordered
  counterclockwise about the ORIGIN; ring edge i joins c_i to c_{i+1}.

DEFINITIONS.  For a hub H and ring vertex c,
      s_H(c) = arccos(|H-c| / (2R))        (real exactly when |H-c| <= 2R)
      cap_H(edge i) = s_H(c_i) + s_H(c_{i+1})
A ring edge is H-LEGAL iff cap_H(edge) is real (both spokes <= 2R).  A hub can realise the
face (H,c_i,c_{i+1}) only on its legal edges, and the face has circumradius <= R exactly
when the turn satisfies theta_i^H <= cap_H(edge i).

FACT 1 (circumradius criterion; elementary, proved in the note).
FACT 2 (ring arithmetic).  For any hub H whose spokes point at the ring once,
      sum_{edges} theta_i^H = 2*pi.
      Consequently, on the sub-chain between two consecutive ring vertices where the
      spokes pass through the ORIGIN, the turns telescope so that
      (sum over a contiguous sub-chain of theta_i^H) = 2*pi - (turns at the sub-chain's
      two ends) = 2*pi - alpha_1 - alpha_2.
FACT 3 (forced cluster structure).  Empirically at the sharp configuration, the legal
      edges of A and of B form two complementary contiguous CLUSTERS (arcs) of the 9-cycle,
      A on the vertices 4,9,10,3 with the outer edges 4-9, 9-10, 10-3, 3-5, 6-4 and
      B on 3,5,7,1,8,6 with the outer edges 3-5, 5-7, 7-1, 1-8, 8-6, 6-4.  The two shared
      edges are 3-5 and 6-4.

SOUND NECESSARY CONDITION (cluster capacity).  For the hub H serving a contiguous cluster
C of edges with end corners p,q:
      sum_{i in C} cap_H(edge i)  >=  2*pi - alpha_p - alpha_q ,
because the left side bounds the sum of the turns (each turn capped) and the right side is
the exact telescoped turn-sum (Fact 2).  A configuration is EXCLUDED as soon as no legal
assignment of the nine edges to the two hubs satisfies this for both hubs.
"""
import json, numpy as np, itertools
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
o0 = np.argsort(np.arctan2(ring0[:, 1], ring0[:, 0])); ring0 = ring0[o0]; ID0 = ID[o0]
P("POLAR ORDER about origin (index:centre label):")
for i, L in enumerate(ID0):
    P(f"   i={i}: ring centre {L}   pos=({ring0[i,0]:+.6f},{ring0[i,1]:+.6f})   |c|={np.linalg.norm(ring0[i]):.6f}")

def sH(H, c, R):
    d = np.linalg.norm(np.asarray(c) - H)
    return np.arccos(np.clip(d / (2 * R), -1, 1)) if d <= 2 * R else np.inf

def report(R, ring, IDv, hA, hB, tag):
    P(f"\n===== {tag}   R = {R:.17f} =====")
    P("   i  edge      |A-c_i|  |B-c_i|    s_A(c_i)  s_B(c_i)   cap_A(i)  cap_B(i)")
    capA, capB = [], []
    for i in range(9):
        j = (i + 1) % 9
        sa1, sa2 = sH(hA, ring[i], R), sH(hA, ring[j], R)
        sb1, sb2 = sH(hB, ring[i], R), sH(hB, ring[j], R)
        ca = sa1 + sa2 if np.isfinite(sa1 + sa2) else np.inf
        cb = sb1 + sb2 if np.isfinite(sb1 + sb2) else np.inf
        capA.append(ca); capB.append(cb)
        f = lambda v: ("   inf  " if not np.isfinite(v) else f"{v:8.5f}")
        P(f"   {i}  {IDv[i]:>2d}-{IDv[j]:<2d}   {np.linalg.norm(ring[i]-hA):7.4f} {np.linalg.norm(ring[i]-hB):7.4f}"
          f"   {f(sa1)} {f(sb1)}   {f(ca)} {f(cb)}")
    la = [i for i in range(9) if np.isfinite(capA[i])]
    lb = [i for i in range(9) if np.isfinite(capB[i])]
    P(f"   A-legal edges: {la}    sum cap_A = {sum(capA[i] for i in la):.8f}")
    P(f"   B-legal edges: {lb}    sum cap_B = {sum(capB[i] for i in lb):.8f}")
    P(f"   covered by at least one hub: {sorted(set(la)|set(lb))}  (all nine = {sorted(set(la)|set(lb))==list(range(9))})")
    # real turns for both hubs
    def turns(H):
        t = np.arctan2(*(ring - H).T)
        return (np.roll(t, -1) - t) % (2 * np.pi)
    tA, tB = turns(hA), turns(hB)
    P(f"   sum tA = {tA.sum():.10f}   sum tB = {tB.sum():.10f}   (2pi = {2*np.pi:.10f})")
    P("   actual turns:  tA: " + " ".join(f"{v:7.4f}" for v in tA))
    P("                  tB: " + " ".join(f"{v:7.4f}" for v in tB))
    P("   cap vs turn (A): " + " ".join(("  --  " if not np.isfinite(capA[i]) else f"{capA[i]-tA[i]:+7.4f}") for i in range(9)))
    P("   cap vs turn (B): " + " ".join(("  --  " if not np.isfinite(capB[i]) else f"{capB[i]-tB[i]:+7.4f}") for i in range(9)))
    return capA, capB, tA, tB

capA, capB, tA, tB = report(Rc, ring0, ID0, HA, HB, "CERTIFIED CANDIDATE")
P("\n  INTERPRETATION: for hub A the binding cluster is the contiguous arc 4-9-10-3 plus")
P("  the shared edges 3-5 and 6-4; the capacity is compared with the telescoped turn sum.")
# cluster capacity check on the candidate's actual clusters (as vertex sets)
clusters = {"A": ([4, 9, 10, 3], [0, 1, 2, 3, 8]), "B": ([3, 5, 7, 1, 8, 6], [3, 4, 5, 6, 7, 8])}
P("\n  cluster capacity ledger (candidate):")
for nm, (verts, edges) in clusters.items():
    cap = capA if nm == "A" else capB
    tt = tA if nm == "A" else tB
    tot = sum(cap[i] for i in edges if np.isfinite(cap[i]))
    actual = sum(tt[i] for i in edges)
    P(f"    hub {nm}: vertices {verts} edges {edges}")
    P(f"       sum cap over cluster = {tot:.8f}   sum actual turns over cluster = {actual:.8f}"
      f"   slack(cap - 2pi) = {tot-2*np.pi:+.6f}")
    P(f"       cluster is contiguous: {edges == list(range(min(edges),max(edges)+1))}")

P("\n=== GLOBAL TEST: can a legal-looking configuration push both cluster slacks below 0? ===")
P("   random sampling of legal geometric configurations (hub cells in B(0,1-R), ring sites")
P("   in the annulus [1-R,1]), computing the best legal assignment and its slack.")
rng = np.random.default_rng(11)
best_excl = None
minslack = 1e9
for trial in range(120000):
    R = 0.38
    hA = rng.uniform(-1, 1, 2) * (1 - R) * 0.95
    hB = rng.uniform(-1, 1, 2) * (1 - R) * 0.95
    th = rng.uniform(0, 2 * np.pi, 9)
    rho = np.sqrt(rng.uniform((1 - R) ** 2, 1.0, 9))
    ring = np.stack([rho * np.cos(th), rho * np.sin(th)], 1)
    o = np.argsort(np.arctan2(ring[:, 1], ring[:, 0])); ring = ring[o]
    ca = np.array([sH(hA, ring[i], R) + sH(hA, ring[(i + 1) % 9], R) for i in range(9)])
    cb = np.array([sH(hB, ring[i], R) + sH(hB, ring[(i + 1) % 9], R) for i in range(9)])
    tt = np.arctan2(*(ring - hA).T); tA_ = (np.roll(tt, -1) - tt) % (2 * np.pi)
    tt = np.arctan2(*(ring - hB).T); tB_ = (np.roll(tt, -1) - tt) % (2 * np.pi)
    # each edge must be legal for >=1 hub, and its turn must be capped by the hub it uses
    feas = True
    for i in range(9):
        okA = np.isfinite(ca[i]) and ca[i] >= tA_[i] - 1e-12
        okB = np.isfinite(cb[i]) and cb[i] >= tB_[i] - 1e-12
        if not (okA or okB):
            feas = False; break
    if not feas:
        continue
    slack = min(ca[np.isfinite(ca)].sum() - 2 * np.pi, cb[np.isfinite(cb)].sum() - 2 * np.pi)
    if slack < minslack:
        minslack = slack; best_excl = (R, hA.copy(), hB.copy(), ring.copy())
P(f"  sampled legal configurations: min over samples of min(sum ca - 2pi, sum cb - 2pi) = {minslack:+.6f}")
P(f"  (candidate value: {min(capA[np.isfinite(capA)].sum(), capB[np.isfinite(capB)].sum())-2*np.pi:+.6f})")

(OUT / "final_experiment.txt").write_text("\n".join(log) + "\n")
P("\nwrote " + str(OUT / "final_experiment.txt"))
