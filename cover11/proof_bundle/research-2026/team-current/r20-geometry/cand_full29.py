"""End-to-end validation + witness computation.

(1) Evaluate ALL 29 frozen-dual atoms at the local data of the CERTIFIED cover
    (n11/upper/certified_object.json): sectors (alpha,u,v), switches (b,s), faces
    (angles, rho/R).  Add the dual constant.  A valid dual must give  area = pi <= total.
(2) Report the seven-factor part J(x*) and the threshold
        T = pi - (const + sum22) = 28.10704541577262956809
    that the flat-exclusion program needs (ROUND15-CONVEY-HUB-LENS).
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
Z = L.ZF

# abstract -> actual centre index
AMAP = {0: 5, 1: 7, 2: 1, 3: 8, 4: 6, 5: 4, 6: 9, 7: 10, 8: 3, 9: 2, 10: 0}
# switch pairs: P_i = tie between rings i and i+1 (mod 9)
PAIR = [(i, (i + 1) % 9) for i in range(9)]


def tie_point(i, j, hint_deg):
    ci, cj = C[i], C[j]
    m = 0.5 * (ci + cj)
    n = (cj - ci) / np.linalg.norm(cj - ci)
    e = np.array([-n[1], n[0]])
    b = 2 * m.dot(e)
    c = m.dot(m) - 1
    disc = b * b - 4 * c
    out = []
    for t in [(-b + math.sqrt(disc)) / 2, (-b - math.sqrt(disc)) / 2]:
        x = m + t * e
        out.append((x, math.degrees(math.atan2(x[1], x[0]))))
    best = min(out, key=lambda q: (lambda d: min(d, 360 - d))(abs(q[1] - hint_deg) % 360))
    return best[0]


# measured arc boundaries (deg) from the nearest-owner partition
HINT = [23.804, 67.694, 112.181, 156.071, 188.251, 227.309, 269.938, 312.567, 351.625]
P = [tie_point(AMAP[i], AMAP[(i + 1) % 9], HINT[i]) for i in range(9)]


def sector_data_geom(c, Pa, Pb):
    u = float(np.linalg.norm(Pa - c)) / R
    v = float(np.linalg.norm(Pb - c)) / R
    va, vb = Pa - c, Pb - c
    al = math.atan2(abs(va[0] * vb[1] - va[1] * vb[0]), float(va.dot(vb)))
    return al, u, v


sectors = []
for i in range(9):
    c = C[AMAP[i]]
    sectors.append(sector_data_geom(c, P[(i - 1) % 9], P[i]))
switches = []
for i in range(9):
    ci, cj = C[AMAP[i]], C[AMAP[(i + 1) % 9]]
    vi, vj = ci - P[i], cj - P[i]
    b = 0.5 * math.atan2(abs(vi[0] * vj[1] - vi[1] * vj[0]), float(vi.dot(vj)))
    s = (np.linalg.norm(vi) + np.linalg.norm(vj)) / (2 * R)
    switches.append((b, s))
faces = []
for f in L.FACES:
    tri = [AMAP[k] for k in f]
    pts = C[tri]
    ang = []
    for k in range(3):
        o, a, b = pts[k], pts[(k + 1) % 3], pts[(k + 2) % 3]
        u, v = a - o, b - o
        ang.append(math.atan2(abs(u[0] * v[1] - u[1] * v[0]), float(u.dot(v))))
    # circumradius: side opposite vertex k, consistency over k = 0,1,2
    rhos = [np.linalg.norm(pts[(k + 1) % 3] - pts[(k + 2) % 3]) / (2 * math.sin(ang[k])) for k in range(3)]
    assert max(rhos) - min(rhos) < 1e-12, (f, rhos)
    faces.append((ang, rhos[0] / R))

print("sector data (alpha, u, v) and r = R t:")
for i, (al, u, v) in enumerate(sectors):
    print("  ring %d: alpha=%.9f u=%.12f v=%.12f" % (i, al, u, v))
print("\nswitches (b, s):")
for i, (b, s) in enumerate(switches):
    print("  switch %d: b=%.9f s=%.12f" % (i, b, s))
print("\nfaces (angles, rho/R):")
for fi, (ang, rn) in enumerate(faces):
    print("  face %2d: angles %s  rho/R=%.9f  sum=%.12f" % (fi, [round(x, 6) for x in ang], rn, sum(ang)))

# ratio check: max geometric radius = covering radius
worst = max(max(ang) for ang, rn in faces)
print("\nmax face angle:", worst)

# ------------- 29 atoms -----------------------------------------------------------------
tot = 0.0
vals = []
for fi in range(11):
    v = L.value(fi, [faces[fi][0][0], faces[fi][0][1], faces[fi][1]])
    # atom expects (angle1, angle2, rho/R) with angle3 = pi - a - b ; every face is a
    # triangle so this is consistent; use angles in the frozen face order
    v = L.value(fi, [faces[fi][0][0], faces[fi][0][1], faces[fi][1]])
    vals.append(v)
    tot += v
for i in range(9):
    v = L.value(11 + i, [switches[i][0], switches[i][1]])
    vals.append(v)
    tot += v
for i in range(9):
    v = L.value(20 + i, [sectors[i][0], sectors[i][1], sectors[i][2]])
    vals.append(v)
    tot += v

# dual constant (LOCAL-Q0-FLAT-EXCLUSION.md, from certify_q0_closure.py)
const = PI * (Z[0:9].sum() + 2 * Z[9:11].sum()) - PI * Z[112:121].sum()
print("\nconst (dual)          = %.15f" % const)
print("sum of 29 atom values = %.15f" % tot)
print("const + sum           = %.15f     (pi = %.15f)" % (const + tot, PI))
print("=> dual inequality pi <= const+sum :", (cond := const + tot >= PI - 1e-12), "  slack = %.6e" % (const + tot - PI))

J = sum(vals[1:3]) + sum(vals[12:14]) + sum(vals[21:24])
S22 = tot - J
print("\nseven-factor J(x*)    = %.15f" % J)
print("22-factor part        = %.15f" % S22)
const22 = const + S22
print("const + 22            = %.15f" % const22)
print("threshold T = pi - (const+sum22sup) = 28.10704541577262956809   [ROUND15]")
print("J(x*) - T             = %+.6e" % (J - 28.10704541577262956809))
print("J(x*) - certified flat ub (high bearing 28.106948822740861261) = %+.6e"
      % (J - 28.106948822740861261))
print("J(x*) - numeric flat max (28.104237014746577) = %+.6e" % (J - 28.104237014746577))

# ------------- relabelled local seven-factor data (for the general chart) --------------
# sector 2 = abstract ring 2 (= actual centre 1), as used by the charts
i2 = 2
p = dict(t=(sectors[i2][1]) / 1.0 * 0 + R * (switches[1][1] * 0 + 1) * 0, a1=0, u1=0, s1=0, a2=0, s2=0, a3=0, v3=0, A=0, H=0)
out = dict(
    sectors=sectors, switches=switches, faces=[(list(a), r) for a, r in faces],
    const=const, total=const + tot, J=J, S22=S22,
    t_sector2=(sectors[2][1]),  # u2 = t (all tight)
    seven=dict(
        faces=[(faces[1][0][0], faces[1][0][1], faces[1][1]), (faces[2][0][0], faces[2][0][1], faces[2][1])],
        switches=[switches[1], switches[2]],
        sectors=[sectors[1], sectors[2], sectors[3]]),
)
json.dump(out, open(HERE / "cand_full29.json", "w"), indent=1)
print("\nwrote cand_full29.json")
