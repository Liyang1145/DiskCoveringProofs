"""Candidate local sector-2 data of the CERTIFIED cover, evaluated in the frozen-dual
seven-factor relaxation.

Certified object: n11/upper/certified_object.json (integer centres / 1e17, certified
covering-radius interval [0.3799838531198387090485..., 0.3799838531198387090485...89]).
All nine switch points turn out to lie at distance exactly the covering radius
(doubly tight configuration).

Local graph (from the nearest-owner arcs and the Delaunay edges of the centres):
  hubs: centres 0 (|c|=0.1494, degree 7) and 2 (|c|=0.2730, degree 6);
  A-chain (hub 2): rings 5 - 7 - 1 - 8 - 6 ; middle ring = 1  => sector 2.
  sector 1 = ring 7, sector 3 = ring 8.
"""
import json, io, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
PI, R = L.PI, L.R
obj = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
sc = 10 ** int(obj["decimals"])
C = np.array([[int(a), int(b)] for a, b in obj["centers_scaled_1e17"]], dtype=float) / sc
RD_LO = float(obj["certified_interval"]["lo"])

HUB = 2          # A-chain hub (5 ring neighbours)
R2 = 1           # middle ring of the A-chain  -> sector 2
RL = 7           # left neighbour  -> sector 1
RR = 8           # right neighbour -> sector 3
PL = (5, 7)      # switch pair left  (P0)
P1 = (7, 1)      # switch pair left-inner (P1)
P2 = (1, 8)      # switch pair right-inner (P2)
PR = (8, 6)      # switch pair right (P3)


def tie(i, j):
    ci, cj = C[i], C[j]
    m = 0.5 * (ci + cj)
    n = (cj - ci) / np.linalg.norm(cj - ci)
    e = np.array([-n[1], n[0]])
    b = 2 * m.dot(e)
    c = m.dot(m) - 1
    disc = b * b - 4 * c
    if disc < 0:
        return None
    out = []
    for t in [(-b + math.sqrt(disc)) / 2, (-b - math.sqrt(disc)) / 2]:
        x = m + t * e
        out.append((x, math.atan2(x[1], x[0]), float(np.linalg.norm(ci - x))))
    return out


def pick(i, j, deg_center):
    best = None
    for (x, ang, rad) in tie(i, j):
        d = abs(math.degrees(ang) - deg_center)
        d = min(d, 360 - d)
        if best is None or d < best[0]:
            best = (d, x, ang, rad)
    return best[1], best[2], best[3]


P0, a0, r0 = pick(*PL, 23.804)
Pp1, a1, r1 = pick(*P1, 67.694)
Pp2, a2, r2 = pick(*P2, 112.181)
P3, a3, r3 = pick(*PR, 156.071)
c2 = C[R2]
c1 = C[RL]
c3 = C[RR]
hub = C[HUB]

print("switch radii  P0..P3:", r0, r1, r2, r3, " covering radius lo:", RD_LO)


def sector(c, Pa, Pb):
    u = float(np.linalg.norm(Pa - c)) / R
    v = float(np.linalg.norm(Pb - c)) / R
    va, vb = Pa - c, Pb - c
    alpha = math.atan2(abs(va[0] * vb[1] - va[1] * vb[0]), float(va.dot(vb)))
    return u, v, alpha


u1, v1, a1ang = sector(c1, P0, Pp1)
u2, v2, a2ang = sector(c2, Pp1, Pp2)
u3, v3, a3ang = sector(c3, Pp2, P3)
t = RD_LO / R
print("\nsector 1: u=%.15f v=%.15f (t=%.15f) alpha=%.15f" % (u1, v1, t, a1ang))
print("sector 2: u=%.15f v=%.15f            alpha=%.15f" % (u2, v2, a2ang))
print("sector 3: u=%.15f v=%.15f            alpha=%.15f" % (u3, v3, a3ang))
print("pi - alpha2 =", PI - a2ang)

# switch half-angles from the geometry: angle at the switch between the two centres
def halfangle(i, j, P):
    vi, vj = C[i] - P, C[j] - P
    return 0.5 * math.atan2(abs(vi[0] * vj[1] - vi[1] * vj[0]), float(vi.dot(vj)))


b1g = halfangle(RL, R2, Pp1)
b2g = halfangle(R2, RR, Pp2)
print("\ngeometric switch half-angles: b1=%.15f b2=%.15f  T=b1+b2=%.15f  pi/2-T=%.6f"
      % (b1g, b2g, b1g + b2g, PI / 2 - (b1g + b2g)))

# face geometry at the A-chain hub
def face_angles(h, i, j):
    """triangle (hub h, ring i, ring j); report the three angles and circumradius"""
    Ph, Pi_, Pj = C[h], C[i], C[j]
    def ang(x, y, z):
        u, v = y - x, z - x
        return math.atan2(abs(u[0] * v[1] - u[1] * v[0]), float(u.dot(v)))
    A = ang(Pj, Pi_, Ph)   # at ring j
    B = ang(Pi_, Pj, Ph)   # at ring i
    Hh = ang(Pi_, Ph, Pj)  # at hub
    a = np.linalg.norm(Pi_ - Ph)
    rho = a / (2 * math.sin(B))
    return B, A, Hh, rho


Bf1, Af1, Hf1, rho1 = face_angles(HUB, RL, R2)
Bf2, Af2, Hf2, rho2 = face_angles(HUB, R2, RR)
print("face1 (hub,ring7,ring1): angle@ring7=%.15f angle@ring1=%.15f angle@hub=%.15f rho/R=%.15f"
      % (Bf1, Af1, Hf1, rho1 / R))
print("face2 (hub,ring1,ring8): angle@ring1=%.15f angle@ring8=%.15f angle@hub=%.15f rho/R=%.15f"
      % (Bf2, Af2, Hf2, rho2 / R))
Hdist = float(np.linalg.norm(hub - c2))
print("H = |hub - c2| = %.15f ; |hub| = %.15f ; 1-r = %.15f" % (Hdist, np.linalg.norm(hub), 1 - RD_LO))

# ---------------- evaluate the seven frozen atoms -------------------------------------
p = dict(t=t, a1=a1ang, u1=u1, s1=v1, a2=a2ang, s2=v2, a3=a3ang, v3=v3,
         A=Af1, H=Hdist)
d = L.gen_args(p)
print("\ngen_args ok:", d is not None)
if d is not None:
    print("  chart b1=%.15f (geom %.15f)  b2=%.15f (geom %.15f)" % (d["b1"], b1g, d["b2"], b2g))
    print("  chart D1=%.15f (geom %.15f)  D2=%.15f (geom %.15f)"
          % (d["D1"], np.linalg.norm(c1 - c2), d["D2"], np.linalg.norm(c3 - c2)))
    print("  chart B=%.15f (geom %.15f)" % (d["B"], Bf2))
    names, mg = L.gen_margins(p, d)
    print("  min margin %.3e  argmin %s" % (min(mg), names[int(np.argmin(mg))]))
    for nm, m in zip(names, mg):
        if m < 2e-3:
            print("     tight %-10s %.4e" % (nm, m))
    J = L.gen_value(d)
    print("\n  J(candidate sector-2 data) = %.15f" % J)
    print("  flat program threshold  pi - (const+sum22) = 28.10704541577262956809")
    print("  certified flat upper bounds: 28.106948822740861261 (high bearing), 28.106833 (both-low collar)")
    print("  numeric flat max (this work, 3 starts)      = 28.104237014746577")
    print("  J - threshold = %.6e" % (J - 28.10704541577262956809))
    # per-atom breakdown
    for fi, x in zip(L.SEVEN_FACES, d["faces"]):
        print("   face   %2d  %s -> %+.12f" % (fi, [round(float(q), 9) for q in x], L.value(fi, x)))
    for fi, x in zip(L.SEVEN_SWITCH, d["switches"]):
        print("   switch %2d  %s -> %+.12f" % (fi, [round(float(q), 9) for q in x], L.value(fi, x)))
    for fi, x in zip(L.SEVEN_SECTOR, d["sectors"]):
        print("   sector %2d  %s -> %+.12f" % (fi, [round(float(q), 9) for q in x], L.value(fi, x)))
    print("   sum = %+.12f" % J)
    json.dump(dict(t=t, a1=a1ang, u1=u1, s1=v1, a2=a2ang, s2=v2, a3=a3ang, v3=v3, A=Af1, H=Hdist,
                   J=J, b1_geom=b1g, b2_geom=b2g, RD_LO=RD_LO,
                   margins={n: float(m) for n, m in zip(names, mg)}),
              open(HERE / "cand_local_data.json", "w"), indent=1)
    print("wrote cand_local_data.json")
