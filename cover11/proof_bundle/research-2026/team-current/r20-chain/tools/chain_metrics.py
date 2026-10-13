"""r20-chain: exact chain/fan measurements on the certified candidate.

Canonical order (counterclockwise about the origin), shared endpoints first:
    ring order:  X = 4, then 9, 10, 3  ->  Y = 3    (hub-0 fan, 4 ring edges / 4 faces)
                 Y = 3, then 5, 7, 1, 8, 6  ->  X = 4 (hub-2 fan, 5 ring edges / 5 faces)

Quantities (all at the certified R, 50 dps):
  spoke  rho_i = |H - c_i|,  deficit  s_i = arccos(rho_i/(2R))  in (0,pi/2)
  local turn  theta_i  between consecutive spokes (oriented)
  face value      T_i = 2R^2 cos s_i cos s_{i+1} sin theta_i        (area of face i)
  face envelope   Fmax_i = 2R^2 max_{s,t in [L,U]} cos s cos t sin(s+t)  (chain-relaxed cap)
  CLOSURE identity  theta_i = s_i + s_{i+1}  <=> the face is at its circumradius R exactly
  fan-arc closure   sum of turns + endpoint angles = 2pi
Area accounting:  sum face areas + sum(ring disk cap over each boundary chord) == pi
"""
import json
from pathlib import Path
from mpmath import mp, mpf, sqrt, cos, sin, acos, asin, atan2, pi, fabs, nstr

mp.dps = 50
HERE = Path(__file__).resolve().parent
OBJ = HERE.parent.parent / "cline2-sharp-fan" / "out" / "certified_object_copy.json"
OUT = HERE.parent / "out"
log = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); log.append(s)

obj = json.loads(OBJ.read_text(encoding="utf-8"))
sc = mpf(10) ** 17
C = [(mpf(int(a)) / sc, mpf(int(b)) / sc) for a, b in obj["centers_scaled_1e17"]]
R = mpf(obj["certified_interval"]["lo"])

def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def dot(a, b): return a[0] * b[0] + a[1] * b[1]
def crs(a, b): return a[0] * b[1] - a[1] * b[0]
def dd(a, b): return sqrt(dot(sub(a, b), sub(a, b)))
def ang(a, b):                       # unsigned angle in [0,pi] between vectors
    c = dot(a, b) / (sqrt(dot(a, a)) * sqrt(dot(b, b)))
    return acos(max(mpf(-1), min(mpf(1), c)))

HA, HB = 0, 2                          # hubs
FANA = [4, 9, 10, 3]                   # c_0 -> c_1 -> c_2 -> c_3   (chain of 4 ring edges)
FANB = [3, 5, 7, 1, 8, 6, 4]           # chain of 5 ring edges
P("R =", nstr(R, 40))
P("hub A =", HA, " |hA| =", nstr(dd(C[HA], (0, 0)), 18))
P("hub B =", HB, " |hB| =", nstr(dd(C[HB], (0, 0)), 18))

# ---------- 1. spoke deficits and turns ----------
def chain_report(hub, chain, name):
    P(f"\n===== {name}: hub {hub}, chain {chain} ({len(chain)-1} ring edges) =====")
    v = [sub(C[i], C[hub]) for i in chain]
    rho = [sqrt(dot(x, x)) for x in v]
    s = [acos(x / (2 * R)) for x in rho]          # deficits
    th = [ang(v[i], v[i + 1]) for i in range(len(chain) - 1)]
    # orientation (is the chain angularly monotone about the hub?)
    signs = [crs(v[i], v[i + 1]) for i in range(len(chain) - 1)]
    P("   orientation signs (cross products):", [("+" if x > 0 else "-") for x in signs])
    for k, i in enumerate(chain):
        P(f"   ring {i:>2d}: rho = {nstr(rho[k],16)}   s = {nstr(s[k],16)} rad   (s/pi = {nstr(s[k]/pi,12)})")
    P("   --- faces ---")
    tot = mpf(0)
    for i in range(len(chain) - 1):
        a, b = s[i], s[i + 1]
        thr = th[i]
        # face area = (1/2) rho_i rho_j sin theta = 2R^2 cos a cos b sin(theta)
        T = 2 * R * R * cos(a) * cos(b) * sin(thr)
        tot += T
        lo, hi = abs(a - b), a + b
        # circumradius of the face triangle (hub, ring_i, ring_j)
        d = dd(C[chain[i]], C[chain[i + 1]])
        cc = (R * R) * cos(a) * cos(b) * sin(thr) / (2 * R * R * cos(a) * cos(b) * sin(thr))  # =1/4 rho_i rho_j sin/R^2
        rhoi, rhoj = rho[i], rho[i + 1]
        K = rhoi * rhoj * sin(thr) / 2
        circ = rhoi * rhoj * d / (4 * K) if K > 0 else None
        P(f"   face {chain[i]:>2d}-{chain[i+1]:<2d}: theta = {nstr(thr,14)}  in ({nstr(lo,10)},{nstr(hi,10)})"
          f"   T = {nstr(T,14)}   circR = {nstr(circ,14)}  (R-circ = {nstr(R-circ,6)})"
          f"   slack_hi = {nstr(hi-thr,8)} slack_lo = {nstr(thr-lo,8)}")
    P("   sum of face areas T_sum =", nstr(tot, 20))
    return v, rho, s, th, tot

vA, rhoA, sA, thA, TA = chain_report(HA, FANA, "FAN A")
vB, rhoB, sB, thB, TB = chain_report(HB, FANB, "FAN B")

# ---------- 2. closure identity per face: theta = s_i + s_j  <=>  face circumradius = R ----------
P("\n===== per-face circumradius (are faces tight?) =====")
def tight_report(hub, chain, name):
    for i in range(len(chain) - 1):
        d = dd(C[chain[i]], C[chain[i + 1]])
        v1, v2 = sub(C[chain[i]], C[hub]), sub(C[chain[i + 1]], C[hub])
        K = crs(v1, v2) / 2
        circ = dd(C[hub], C[chain[i]]) * dd(C[hub], C[chain[i + 1]]) * d / (4 * abs(K))
        P(f"   {name} face ({hub},{chain[i]},{chain[i+1]}): circR = {nstr(circ,18)}   R - circR = {nstr(R-circ,8)}")
tight_report(HA, FANA, "A")
tight_report(HB, FANB, "B")

# ---------- 3. total turn identity: Sigma theta + endpoint angles = 2pi ----------
P("\n===== total-turn accounting =====")
E = dd(C[HA], C[HB])
for nm, hub, chain, th in (("A", HA, FANA, thA), ("B", HB, FANB, thB)):
    z = sub(C[HB], C[HA]) if nm == "A" else sub(C[HA], C[HB])
    first, last = (sub(C[chain[0]], C[hub]) if nm == "A" else sub(C[chain[-1]], C[hub])), \
                  (sub(C[chain[-1]], C[hub]) if nm == "A" else sub(C[chain[0]], C[hub]))
    a_first = ang(z, first)     # angle at hub between hub-hub spoke and the first chain spoke
    a_last = ang(z, last)
    P(f"   fan {nm}: sum theta = {nstr(sum(th),18)}   endpoint angles = ({nstr(a_first,14)}, {nstr(a_last,14)})")
    P(f"           sum theta + a_first + a_last = {nstr(sum(th)+a_first+a_last,18)}   (2pi = {nstr(2*pi,18)})")
    P(f"           deficit = {nstr(2*pi-(sum(th)+a_first+a_last),12)}")

# ---------- 4. endpoint triangle (A,B,endpoint) ----------
P("\n===== endpoint triangles (A,B,endpoint) =====")
E = dd(C[HA], C[HB])
for i in (4, 3):
    rA, rB = dd(C[HA], C[i]), dd(C[HB], C[i])
    K = crs(sub(C[HA], C[i]), sub(C[HB], C[i])) / 2
    circ = rA * rB * E / (4 * abs(K))
    P(f"   endpoint {i}: |A-{i}|={nstr(rA,16)} |B-{i}|={nstr(rB,16)} |A-B|={nstr(E,16)}  circR={nstr(circ,18)}  R-circR={nstr(R-circ,8)}")
    P(f"      angle at A = {nstr(ang(sub(C[HB],C[HA]), sub(C[i],C[HA])),14)}   angle at B = {nstr(ang(sub(C[HA],C[HB]), sub(C[i],C[HB])),14)}")

# ---------- 5. endpoint spoke deficits: the entry/exit of each chain ----------
P("\n===== spoke deficit table (all nine rings, both hubs) =====")
for hub, nm in ((HA, "A"), (HB, "B")):
    row = []
    for i in range(11):
        if i in (HA, HB): continue
        row.append((i, acos(dd(C[hub], C[i]) / (2 * R))))
    P(f"   hub {nm}:", ", ".join(f"{i}:{nstr(x,10)}" for i, x in sorted(row)))

# ---------- 6. exact area accounting s.t. total == pi ----------
P("\n===== area accounting =====")
# Delaunay faces (order independent sum of face areas) via the two fans' faces
del_faces = [(HA, 9, 10), (HA, 3, 5), (HA, 4, 6), (HA, 2, 5), (HA, 2, 6), (HA, 3, 10), (HA, 4, 9),
             (HB, 5, 7), (HB, 6, 8), (HB, 1, 8), (HB, 1, 7)]
tot_tri = mpf(0)
for f in del_faces:
    a, b, c = (C[i] for i in f)
    tot_tri += abs(crs(sub(b, a), sub(c, a))) / 2
P("   sum of the 11 face areas =", nstr(tot_tri, 20))
# segment areas over the nine boundary chords, using the polar order
order = [4, 9, 10, 3, 5, 7, 1, 8, 6]
tot_seg = mpf(0)
for k in range(9):
    i, j = order[k], order[(k + 1) % 9]
    w = atan2(crs(C[i], C[j]), dot(C[i], C[j]))
    if w < 0: w += 2 * pi
    tot_seg += (w - sin(w)) / 2
P("   sum of the 9 circular-segment areas =", nstr(tot_seg, 20))
P("   triangle + segment =", nstr(tot_tri + tot_seg, 20), "   pi =", nstr(pi, 20),
  "   difference =", nstr(tot_tri + tot_seg - pi, 6))

(OUT / "chain_metrics.txt").write_text("\n".join(log) + "\n")
P("\nwrote", OUT / "chain_metrics.txt")
