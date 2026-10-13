"""General graph-mapping + full-29 frozen-dual evaluation for any 9+2 configuration.

Mapping is derived from the geometry (nearest-owner arcs + hubs + chains), not hard-wired.
Validation targets:
  * record KKT configuration n11/kkt2/frozen.json  -> joint_nested_frozen.json
    records  numeric_total_unrounded = 3.1378200846693396
  * certified object n11/upper/certified_object.json -> tight at pi
"""
import json, io, math, sys
from pathlib import Path
import numpy as np
from scipy.spatial import Delaunay

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
PI, R = L.PI, L.R
Z = L.ZF


def load_config(name):
    if name == "record":
        d = json.load(io.open(ROOT / "n11/kkt2/frozen.json", encoding="utf-8"))
        C = np.array(d["centers"], dtype=float)
        return C, d.get("R")
    if name == "certified":
        d = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
        sc = 10 ** int(d["decimals"])
        C = np.array([[int(a), int(b)] for a, b in d["centers_scaled_1e17"]], dtype=float) / sc
        return C, float(d["certified_interval"]["lo"])
    raise ValueError(name)


def nearest_runs(C, NS=1 << 18):
    th = np.linspace(0, 2 * math.pi, NS, endpoint=False)
    P = np.c_[np.cos(th), np.sin(th)]
    dd = np.sqrt(((P[:, None, :] - C[None, :, :]) ** 2).sum(-1))
    own = dd.argmin(1)
    runs = []
    s = 0
    for k in range(1, NS + 1):
        if k == NS or own[k % NS] != own[s]:
            runs.append([int(own[s]), s, k])
            s = k
    if len(runs) > 1 and runs[0][0] == runs[-1][0]:
        runs = runs[1:-1] + [[runs[-1][0], runs[-1][1], runs[0][2] + NS]]
    return runs, th, P


def tie_pts(i, j, C):
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
    return out


def ang_dist(a, b):
    d = abs(a - b) % 360
    return min(d, 360 - d)


def build(C):
    NS = 1 << 18
    runs, th, P = nearest_runs(C, NS)
    rings = [r[0] for r in runs]
    mids = [math.degrees((r[1] + r[2]) / 2 * 2 * math.pi / NS) for r in runs]
    hubs = [i for i in range(len(C)) if i not in rings]
    if len(rings) != 9 or len(hubs) != 2:
        return None
    # cyclic order of rings by arc mid angle
    order = [rings[k] for k in sorted(range(len(rings)), key=lambda k: mids[k] % 360)]
    # hub degrees via Delaunay
    tri = Delaunay(C)
    edges = set()
    for s in tri.simplices:
        for a in range(3):
            for b in range(a + 1, 3):
                edges.add(tuple(sorted((int(s[a]), int(s[b])))))
    nbr = {h: [r for r in rings if tuple(sorted((h, r))) in edges] for h in hubs}
    deg = {h: len(nbr[h]) for h in hubs}
    hubA = [h for h in hubs if deg[h] == 5][0]     # 5 ring neighbours -> abstract hub 9
    hubB = [h for h in hubs if deg[h] == 6][0]
    common = [r for r in nbr[hubA] if r in nbr[hubB]]
    # A-chain in cyclic order: start at common[0], walk along `order` through the 5 members
    def chain(hub, start):
        mem = set(nbr[hub])
        idx = order.index(start)
        seq = []
        for k in range(9):
            r = order[(idx + k) % 9]
            if r in mem:
                seq.append(r)
            if len(seq) == len(mem):
                break
        return seq
    A = chain(hubA, common[0])
    if len(A) != 5:
        A = chain(hubA, common[1])
    Bc = chain(hubB, A[-1])
    if len(Bc) != 6 or Bc[-1] != A[0]:
        Bc = chain(hubB, A[-1]) if len(chain(hubB, A[-1])) == 6 else None
    if Bc is None:
        return None
    AMAP = {i: A[i] for i in range(5)}
    for j in range(1, 5):
        AMAP[4 + j] = Bc[j]
    AMAP[9] = hubA
    AMAP[10] = hubB
    return dict(AMAP=AMAP, rings=rings, order=order, hubs=hubs, A=A, B=Bc, runs=runs, NS=NS)


def evaluate(C, g, verbose=False):
    AMAP = g["AMAP"]
    NS = g["NS"]
    # switch points: tie between abstract rings i,i+1 with hint from the measured boundary
    hint = {}
    for k, r in enumerate(g["order"]):
        pass
    Psw = []
    for i in range(9):
        ia, ib = AMAP[i], AMAP[(i + 1) % 9]
        # find the measured boundary angle between the arcs of ia and ib
        mids = {r: math.degrees((run[1] + run[2]) / 2 * 2 * math.pi / NS) for run, r in zip(g["runs"], [q[0] for q in g["runs"]])}
        cand = tie_pts(ia, ib, C)
        # pick the root that lies between the two arc midpoints (angularly closest to both)
        best, bk = None, 1e9
        ma, mb = mids.get(ia), mids.get(ib)
        if ma is None or mb is None:
            return None
        mid_target = math.degrees(math.atan2(
            (math.sin(math.radians(ma)) + math.sin(math.radians(mb))) / 2,
            (math.cos(math.radians(ma)) + math.cos(math.radians(mb))) / 2))
        for (x, a) in cand:
            k = ang_dist(a, mid_target)
            if k < bk:
                bk, best = k, x
        Psw.append(best)
    sectors = []
    for i in range(9):
        c = C[AMAP[i]]
        Pa, Pb = Psw[(i - 1) % 9], Psw[i]
        u = float(np.linalg.norm(Pa - c)) / R
        v = float(np.linalg.norm(Pb - c)) / R
        va, vb = Pa - c, Pb - c
        al = math.atan2(abs(va[0] * vb[1] - va[1] * vb[0]), float(va.dot(vb)))
        sectors.append((al, u, v))
    switches = []
    for i in range(9):
        ci, cj = C[AMAP[i]], C[AMAP[(i + 1) % 9]]
        vi, vj = ci - Psw[i], cj - Psw[i]
        b = 0.5 * math.atan2(abs(vi[0] * vj[1] - vi[1] * vj[0]), float(vi.dot(vj)))
        s = (np.linalg.norm(vi) + np.linalg.norm(vj)) / (2 * R)
        switches.append((b, s))
    faces = []
    for f in L.FACES:
        pts = C[[AMAP[k] for k in f]]
        ang = []
        for k in range(3):
            o, a, b = pts[k], pts[(k + 1) % 3], pts[(k + 2) % 3]
            u, v = a - o, b - o
            ang.append(math.atan2(abs(u[0] * v[1] - u[1] * v[0]), float(u.dot(v))))
        rhos = [np.linalg.norm(pts[(k + 1) % 3] - pts[(k + 2) % 3]) / (2 * math.sin(ang[k])) for k in range(3)]
        faces.append((ang, (sum(rhos) / 3) / R))
    tot = 0.0
    vals = []
    for fi in range(11):
        vals.append(L.value(fi, [faces[fi][0][0], faces[fi][0][1], faces[fi][1]]))
    for i in range(9):
        vals.append(L.value(11 + i, [switches[i][0], switches[i][1]]))
    for i in range(9):
        vals.append(L.value(20 + i, [sectors[i][0], sectors[i][1], sectors[i][2]]))
    tot = sum(vals)
    const = PI * (Z[0:9].sum() + 2 * Z[9:11].sum()) - PI * Z[112:121].sum()
    J = sum(vals[1:3]) + sum(vals[12:14]) + sum(vals[21:24])
    S22 = tot - J
    return dict(total=const + tot, const=const, S22=S22, J=J, sectors=sectors, switches=switches,
                faces=faces, AMAP=AMAP, Psw=Psw, vals=vals)


if __name__ == "__main__":
    for name in ["record", "certified"]:
        C, Rc = load_config(name)
        g = build(C)
        print("==", name, "R =", Rc, " AMAP:", g["AMAP"] if g else None)
        print("   A-chain:", g["A"], " B-chain:", g["B"])
        res = evaluate(C, g)
        print("   const + sum29 = %.15f   (pi = %.15f, slack %+.3e)" % (res["total"], PI, res["total"] - PI))
        print("   J = %.12f   S22 = %.12f" % (res["J"], res["S22"]))
        print("   switch radii:", ["%.12f" % ((lambda a: a)(q)) for q in [np.linalg.norm(C[g["AMAP"][i]] - res["Psw"][i]) for i in range(9)]])
        json.dump(dict(AMAP=g["AMAP"], total=res["total"], J=res["J"], S22=res["S22"],
                       sectors=res["sectors"], switches=res["switches"],
                       faces=[(a, r) for a, r in res["faces"]], R=Rc),
                  open(HERE / ("full29_%s.json" % name), "w"), indent=1)
