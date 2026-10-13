"""r20-chain: THE SATURATION-FREE CLUSTER CAPACITY CRITERION -- final bounded experiment.

Correct angle convention (fixes earlier wrap bugs):
  polar order about the ORIGIN; a "cluster" is a CONTIGUOUS set of ring edges (an arc).
  For hub H and a cluster arc with edge list e = [a..b] (cyclic), define
      cap_H(e)   = sum over e of ( s_H(c_i) + s_H(c_{i+1}) ),   inf if any spoke > 2R
      width_H(e) = sum over e of the SIGNED turn at H from spoke c_i to spoke c_{i+1}
                   = the actual angular width that hub H spans over that arc
                   = (total signed turn round the ring = +-2pi) - (the two outer turns).
  FACT (circumradius criterion): for every edge served by H, turn <= cap on that edge.
  CONSEQUENCE:  width_H(e) <= cap_H(e)   for the arc that H serves.
  Since the ring turns once around each hub, the two arcs left outside a cluster give
      width_H(e) = 2pi - (the two outer corner turns of H),
  so an equivalent form is
      cap_H(e) + (the two corner s-sums of H)  >=  2pi .

EXCLUSION CRITERION TESTED HERE: enumerate the two ways the nine edges can be split into
two contiguous arcs; for each, compute cap_A(arc_A) - width_A(arc_A) and
cap_B(arc_B) - width_B(arc_B).  A configuration is impossible if every split fails.
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
ring = C[ID]
o = np.argsort(np.arctan2(ring[:, 1], ring[:, 0])); ring = ring[o]; IDv = ID[o]

def spoke_caps(H, R):
    s = np.array([(lambda d: np.arccos(np.clip(d / (2 * R), -1, 1)) if d <= 2 * R else np.inf)
                  (np.linalg.norm(c - H)) for c in ring])
    return s

def signed_turns(H):
    """signed turns t_i = angle from spoke i to spoke i+1, principal value; sum = +-2pi."""
    t = np.arctan2(*(ring - H).T)
    d = np.diff(np.append(t, t[0]))          # last one wraps; fix below
    d[-1] = t[0] - t[-1]
    return d

def cluster_slack(H, R, arc):
    """arc = list of edge indices, contiguous). slack = cap - width."""
    s = spoke_caps(H, R)
    cap = np.array([s[i] + s[(i + 1) % 9] for i in range(9)])
    tt = signed_turns(H)
    if not np.all(np.isfinite(cap[arc])):
        return np.inf, np.inf, np.inf
    # the served arc must be traversed in the sign direction where turns are positive
    w = sum(tt[i] for i in arc)
    return cap[arc].sum(), w, cap[arc].sum() - w

P("=== certified candidate ===")
for H, nm in ((HA, "A"), (HB, "B")):
    s = spoke_caps(H, Rc)
    tt = signed_turns(H)
    P(f"\nhub {nm}: s(c_i) = " + " ".join(("%8.5f" % v if np.isfinite(v) else "    inf ") for v in s))
    P(f"         signed turns = " + " ".join("%8.5f" % v for v in tt) + f"   sum = {tt.sum():.6f}")
# cluster A: edges [8,0,1,2,3]; cluster B: edges [4,5,6,7]
arcA = [8, 0, 1, 2, 3]; arcB = [4, 5, 6, 7]
for H, nm, arc in ((HA, "A", arcA), (HB, "B", arcB)):
    cap, w, sl = cluster_slack(H, Rc, arc)
    P(f"  hub {nm}, arc {arc}: cap = {cap:.8f}   width = {w:.8f}   slack = {sl:+.6f}")
    # the complementary (outer) part
    comp = [i for i in range(9) if i not in arc]
    tt = signed_turns(H)
    wcmp = sum(tt[i] for i in comp)
    P(f"     complement edges {comp}: width = {wcmp:.8f}   (2pi - width = {2*np.pi-wcmp:.8f})")
    # corner form
    P(f"     equivalent corner form: cap + corner widths >= 2pi ->"
      f" {cap + wcmp:.8f} >= {2*np.pi:.8f}  slack {cap+wcmp-2*np.pi:+.6f}")

P("\n=== all 9 splits into two contiguous arcs: slack ledger ===")
P("   split(e) means cluster A = edges e .. e+3 (cyclic, 4 edges), cluster B = the other 5")
worst = 1e9
for e in range(9):
    arcA = [(e + k) % 9 for k in range(4)]
    arcB = [(e + 4 + k) % 9 for k in range(5)]
    cA, wA, slA = cluster_slack(HA, Rc, arcA)
    cB, wB, slB = cluster_slack(HB, Rc, arcB)
    ok = np.isfinite(slA) and np.isfinite(slB)
    m = min(slA, slB)
    if ok:
        worst = min(worst, m)
    P(f"   e={e}: A-arc {arcA} cap={cA:7.4f} width={wA:7.4f} slack={slA:+7.4f} | "
      f"B-arc {arcB} cap={cB:7.4f} width={wB:7.4f} slack={slB:+7.4f}  -> min slack {m:+.4f}")
P(f"   WORST min-slack over splits = {worst:+.6f}   (>= 0 means the criterion does NOT exclude)")

P("\n=== global random test of the criterion's margin ===")
rng = np.random.default_rng(5)
worstG = 1e9
for t in range(60000):
    R = 0.38
    hA = rng.uniform(-1, 1, 2) * (1 - R) * .95
    hB = rng.uniform(-1, 1, 2) * (1 - R) * .95
    th = rng.uniform(0, 2 * np.pi, 9); rho = np.sqrt(rng.uniform((1 - R) ** 2, 1, 9))
    r = np.stack([rho * np.cos(th), rho * np.sin(th)], 1)
    oo = np.argsort(np.arctan2(r[:, 1], r[:, 0])); r = r[oo]
    globals()['ring'] = r
    for e in range(9):
        arcA = [(e + k) % 9 for k in range(4)]; arcB = [(e + 4 + k) % 9 for k in range(5)]
        cA, wA, slA = cluster_slack(hA, R, arcA)
        cB, wB, slB = cluster_slack(hB, R, arcB)
        if np.isfinite(slA) and np.isfinite(slB):
            worstG = min(worstG, min(slA, slB))
P(f"   smallest min-slack found = {worstG:+.6f}  (candidate: {worst:+.6f})")
P("   -> the criterion 'cap >= width for both arcs' cannot exclude by itself"
  if worst <= 0 else "   -> criterion margin positive at the candidate")

(OUT / "cluster_criterion.txt").write_text("\n".join(log) + "\n")
P("\nwrote " + str(OUT / "cluster_criterion.txt"))
