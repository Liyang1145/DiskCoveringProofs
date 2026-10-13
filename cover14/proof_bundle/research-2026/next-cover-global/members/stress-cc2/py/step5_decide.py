"""step5_decide.py -- transparent numpy circumcentre check + covering radius, both roots.
Deliberately redundant: (i) circumcentre by 2x2 solve, (ii) distances to all sites,
(iii) max over ALL in-disk circumcentres and over the boundary circle.
"""
import json, sys, itertools
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, old_geom_centers

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

def Cnp_of(C):
    return np.array([[float(c[0]), float(c[1])] for c in C], dtype=float)

def circum_np(P):
    """P: (3,2) -> circumcentre via 2x2 solve"""
    A = 2 * (P[1:] - P[0])
    b = (P[1:] ** 2).sum(1) - (P[0] ** 2).sum()
    try:
        return np.linalg.solve(A, b)
    except np.linalg.LinAlgError:
        return None

def scan(C, tag):
    Cn = Cnp_of(C)
    W("== %s ==" % tag)
    best = (-1, None, None)
    nin = 0
    big = []
    for tri in itertools.combinations(range(14), 3):
        P = Cn[list(tri)]
        u = circum_np(P)
        if u is None:
            continue
        if (u ** 2).sum() > 1.0:
            continue
        nin += 1
        f = np.sqrt(((Cn - u) ** 2).sum(1)).min()
        if f > best[0]:
            best = (f, u, tri)
        if f > 0.3317:
            big.append((float(f), tri, u))
    W("   in-disk circumcentres: %d ; max min-dist = %.18f at tri%s u=(%.15f,%.15f)" % (nin, best[0], best[2], best[1][0], best[1][1]))
    ds = np.sqrt(((Cn - best[1]) ** 2).sum(1))
    W("   nearest sites at that circumcentre: %s" % sorted(zip(ds.round(15), range(14)))[:4])
    W("   #circumcentres with min-dist > 0.3317 : %d" % len(big))
    # boundary
    th = np.linspace(0, 2 * np.pi, 4_000_001)[:-1]
    X = np.stack([np.cos(th), np.sin(th)], 1)
    d = np.sqrt(((X[:, None, :] - Cn[None, :, :]) ** 2).sum(-1)).min(1)
    i = int(d.argmax())
    W("   boundary max min-dist = %.18f at angle %.8f deg  point (%.15f,%.15f)" % (
        d[i], np.degrees(th[i]), X[i, 0], X[i, 1]))
    dsb = np.sqrt(((Cn - X[i]) ** 2).sum(1))
    W("     nearest sites: %s" % sorted(zip(dsb.round(15), range(14)))[:4])
    W("   f(point) grid : max over whole disk (2000^2):")
    g = np.linspace(-1, 1, 2000)
    XX, YY = np.meshgrid(g, g)
    Pm = np.stack([XX.ravel(), YY.ravel()], 1)
    Pm = Pm[(Pm ** 2).sum(1) <= 1.0]
    dm = np.sqrt(((Pm[:, None, :] - Cn[None, :, :]) ** 2).sum(-1)).min(1)
    j = int(dm.argmax())
    W("     grid max = %.18f at (%.12f,%.12f) |x|=%.9f" % (dm[j], Pm[j, 0], Pm[j, 1], np.hypot(*Pm[j])))
    return dict(n_in=nin, max_circ=float(best[0]), argmax_tri=list(map(int, best[2])),
                bd_max=float(d[i]), bd_ang=float(np.degrees(th[i])),
                grid_max=float(dm[j]), grid_arg=[float(Pm[j, 0]), float(Pm[j, 1])])

g = new_geom(); Cnew = centers_from(g)
Cold, Rold, _ = old_geom_centers()
W("declared NEW r* = 0.3317320342762341225578")
W("declared OLD R  = 0.3317320342762341235155")
W("improved upper T (lead) = 0.3317320342762341226")
W("")
a = scan(Cnew, "NEW root geometry (lead root-scout z,c,r)")
W("")
b = scan(Cold, "OLD refined geometry")
W("")
W("VERDICT")
W("  NEW geometry covers D at radius     : %.18f" % max(a["max_circ"], a["bd_max"]))
W("  OLD geometry covers D at radius     : %.18f" % max(b["max_circ"], b["bd_max"]))
json.dump(dict(new=a, old=b), open(HERE.parent / "evidence/step5_decide.json", "w"), indent=1)
(HERE.parent / "logs/step5_decide.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/step5_decide.txt")
