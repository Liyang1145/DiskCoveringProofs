"""r20-chain: clean single-pass measurement (monotone unwrapped turns).

Polar order about the ORIGIN; ring site i has azimuth A_0 < A_1 < ... < A_8 (unwrapped,
A_8 < A_0 + 2pi).  For a hub H let p_i = azimuth of (c_i - H), unwrapped so that the
sequence p_0..p_8 is monotone in the direction of the ring (this is the correct choice for
a legal hub; the region it serves is a single cone).  Then
    turn_i^H = p_{i+1} - p_i   (>0),   sum_i turn_i^H = 2pi  (ring arithmetic).
    width over a contiguous sub-chain [a..b] = p_b - p_a.
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
o = np.argsort(np.arctan2(ring[:, 1], ring[:, 0]))
ring = ring[o]; IDv = ID[o]

def unwrap_about(H, ring, A0):
    """azimuths of ring sites about H, unwrapped to be monotone in the same direction as A0."""
    t = np.arctan2(*(ring - H).T)
    t = np.unwrap(t)                       # ordering by index (index order = polar order about O)
    # ensure increasing
    while t[-1] < t[0]:
        t[-1] += 2 * np.pi
    return t

def sH(H, c, R):
    d = np.linalg.norm(np.asarray(c) - H)
    return np.arccos(np.clip(d / (2 * R), -1, 1)) if d <= 2 * R else np.inf

A0 = np.unwrap(np.arctan2(ring[:, 1], ring[:, 0]))
P("polar azimuths about the origin (unwrapped):")
P("   " + " ".join(f"{v:8.4f}" for v in A0))
P("gaps: " + " ".join(f"{np.diff(np.append(A0,A0[0]+2*np.pi))[i]:7.4f}" for i in range(9)))

rows = {}
for H, nm in ((HA, "A"), (HB, "B")):
    t = unwrap_about(H, ring, A0)
    P(f"\nhub {nm} (centre {0 if nm=='A' else 2}, |h|={np.linalg.norm(H):.6f}):")
    P("   azimuths about hub: " + " ".join(f"{v:9.5f}" for v in t))
    d = np.diff(np.append(t, t[0] + 2 * np.pi))
    P("   turns:             " + " ".join(f"{v:9.5f}" for v in d))
    P(f"   sum of turns = {d.sum():.12f}   (2pi = {2*np.pi:.12f})   deviation = {d.sum()-2*np.pi:+.3e}")
    s = np.array([sH(H, c, Rc) for c in ring])
    P("   s_H(c_i):          " + " ".join(("%9.5f" % v if np.isfinite(v) else "     inf ") for v in s))
    cap = np.array([s[i] + s[(i + 1) % 9] for i in range(9)])
    P("   cap_H(edge i):     " + " ".join(("%9.5f" % v if np.isfinite(v) else "     inf ") for v in cap))
    fin = np.isfinite(cap)
    P(f"   legal edges (cap finite): {list(np.where(fin)[0])}   sum cap over them = {cap[fin].sum():.8f}")
    P(f"   sum of turns over the legal edges  = {d[fin].sum():.8f}"
      f"   (compare: sum cap - sum turn = {cap[fin].sum()-d[fin].sum():+.6f})")
    # contiguity of the legal set (cyclic)
    idx = list(np.where(fin)[0])
    contig = (max(idx) - min(idx) + 1 == len(idx))
    P(f"   legal set contiguous on the 9-cycle: {contig}   -> as a cyclic block: "
      f"{list(range(min(idx),max(idx)+1)) if contig else 'NO'}")
    if contig:
        a, b = min(idx), max(idx)
        width = t[(b + 1) % 9] - t[a] if b + 1 <= 8 else (t[0] + 2 * np.pi) - t[a]
        if b + 1 <= 8:
            width = t[b + 1] - t[a]
        else:
            width = (t[0] + 2 * np.pi) - t[a]
        P(f"   sub-chain edges {a}..{b} spans width = {width:.8f}")
        P(f"   CLUSTER CAPACITY check: sum cap = {cap[fin].sum():.8f}  vs  width = {width:.8f}"
          f"    slack = {cap[fin].sum()-width:+.6f}")
    rows[nm] = dict(turns=d, s=s, cap=cap)

P("\n=== per-edge capacity vs the turn of the SERVING hub (the core inequality) ===")
P("   i  edge      cap_A(i)   tA(i)   slack_A     cap_B(i)   tB(i)   slack_B    serving hub")
for i in range(9):
    ca, cb = rows["A"]["cap"][i], rows["B"]["cap"][i]
    ta, tb = rows["A"]["turns"][i], rows["B"]["turns"][i]
    sa = (ca - ta) if np.isfinite(ca) else None
    sb = (cb - tb) if np.isfinite(cb) else None
    serv = "A" if (sa is not None and sa >= -1e-12) else ("B" if (sb is not None and sb >= -1e-12) else "NONE")
    f = lambda v: ("    --   " if v is None else f"{v:8.5f}")
    P(f"   {i}  {IDv[i]:>2d}-{IDv[(i+1)%9]:<2d}  {f(ca)} {ta:8.5f} {f(sa)}  {f(cb)} {tb:8.5f} {f(sb)}   {serv}")

(OUT / "clean_measurement.txt").write_text("\n".join(log) + "\n")
P("\nwrote " + str(OUT / "clean_measurement.txt"))
