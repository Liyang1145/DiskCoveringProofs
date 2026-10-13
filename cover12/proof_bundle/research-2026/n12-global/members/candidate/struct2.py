"""Step 2b (fast): contact structure using float64 scans for location + mpmath(dps=60)
for the exact-ish residuals of the located objects.  Cheap and complete.

Writes evidence/struct2.txt (append-safe: regenerated whole) and struct2.json.
"""
from pathlib import Path
from fractions import Fraction as F
import json, math

import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
EV.mkdir(parents=True, exist_ok=True)
CFGA = ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json"
CFGB = ROOT / "flash-n11/members/othern-scout/s3/n12_d3_kkt.json"
A = json.loads(CFGA.read_text(encoding="utf-8"))
B = json.loads(CFGB.read_text(encoding="utf-8"))

OUT = []
def W(s=""):
    OUT.append(str(s))

def analyse(tag, cfg, key, Rm):
    cen = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in cfg[key]]
    n = len(cen)
    R = Rm
    W(f"=================== {tag} : n={n}  R(literal)={mp.nstr(R,32)} ===================")
    rad = [mp.sqrt(c[0]**2+c[1]**2) for c in cen]
    ang = [mp.atan2(c[1], c[0]) for c in cen]
    W("-- radius / angle / boundary test --")
    for i in range(n):
        W(f"  {i:2d} rho={mp.nstr(rad[i],30):<34} theta_deg={mp.nstr(ang[i]*180/mp.pi,20):<24}"
          f" rho-(1-R)={mp.nstr(rad[i]-(1-R),8):<14} rho-2R={mp.nstr(rad[i]-2*R,8)}")
    D = [[mp.sqrt((cen[i][0]-cen[j][0])**2+(cen[i][1]-cen[j][1])**2) for j in range(n)] for i in range(n)]
    W("-- tangent pairs |d-2R| < 1e-20 --")
    tan = []
    for i in range(n):
        for j in range(i+1, n):
            if mp.fabs(D[i][j]-2*R) < mp.mpf('1e-20'):
                tan.append((i, j))
                W(f"   ({i:2d},{j:2d}) d={mp.nstr(D[i][j],34)} d-2R={mp.nstr(D[i][j]-2*R,8)}")
    W(f"   -> {len(tan)} tangent pairs: {tan}")
    W("-- 3 nearest neighbours of each centre --")
    for i in range(n):
        order = sorted([j for j in range(n) if j != i], key=lambda j: D[i][j])
        W(f"  {i:2d}: " + "  ".join(f"c{j}({mp.nstr(D[i][j],10)})" for j in order[:3]))
    W("-- all near-degenerate triples: circumradius within 1e-6 of R, circumcentre in D --")
    worsts = []
    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                ax, ay = cen[i]; bx, by = cen[j]; cx, cy = cen[k]
                den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
                if mp.fabs(den) < mp.mpf('1e-30'):
                    continue
                ux = ((ax**2+ay**2-cx**2-cy**2)*(by-cy)-(ay-cy)*(bx**2+by**2-cx**2-cy**2))/den
                uy = ((ax-cx)*(bx**2+by**2-cx**2-cy**2)-(ax**2+ay**2-cx**2-cy**2)*(bx-cx))/den
                rr = mp.sqrt((ux-ax)**2+(uy-ay)**2)
                if mp.fabs(rr-R) < mp.mpf('1e-6'):
                    onb = mp.sqrt(ux**2+uy**2)
                    if onb <= 1:
                        dd = sorted((mp.sqrt((ux-cen[t][0])**2+(uy-cen[t][1])**2), t) for t in range(n))
                        worsts.append({"tri": [i, j, k], "p": [mp.nstr(ux, 24), mp.nstr(uy, 24)],
                                       "|p|": mp.nstr(onb, 20), "rr": mp.nstr(rr, 32),
                                       "rr-R": mp.nstr(rr-R, 8),
                                       "nearest": [[t, mp.nstr(d, 20)] for d, t in dd[:4]]})
                        W(f"   tri({i:2d},{j:2d},{k:2d}) u=({mp.nstr(ux,22)},{mp.nstr(uy,22)}) |u|={mp.nstr(onb,18)}"
                          f" rr-R={mp.nstr(rr-R,6)}  near:" + " ".join(f"c{t}:{mp.nstr(d,18)}" for d, t in dd[:3]))
    W(f"   -> {len(worsts)} such triples")
    # float scans
    Af = [(float(c[0]), float(c[1])) for c in cen]
    Rf = float(R)
    best = (-1, None)
    N = 2_000_000
    import cmath
    for t in range(N):
        th = 2*math.pi*t/N
        px, py = math.cos(th), math.sin(th)
        dm = min(math.dist((px, py), c) for c in Af)
        if dm > best[0]:
            best = (dm, th)
    W(f"-- boundary scan N={N}: max-min = {best[0]:.17g} at theta_deg={best[1]*180/math.pi:.10f}"
      f"   (R={Rf:.17g}, diff={best[0]-Rf:.3e})")
    # interior grid + local polish via 3-disk argmax candidates
    NG = 700
    bestg = (-1, None, None)
    for a in range(NG+1):
        x = -1 + 2*a/NG
        for b in range(NG+1):
            y = -1 + 2*b/NG
            if x*x+y*y > 1: continue
            dm = min(math.dist((x, y), c) for c in Af)
            if dm > bestg[0]:
                bestg = (dm, x, y)
    W(f"-- interior grid({NG}): max-min = {bestg[0]:.17g} at ({bestg[1]:.10f},{bestg[2]:.10f})"
      f"  diff vs R = {bestg[0]-Rf:.3e}")
    return {"tag": tag, "R": mp.nstr(R, 32), "tangent_pairs": tan, "worsts": worsts,
            "boundary_maxmin": repr(best[0]), "boundary_theta": repr(best[1]),
            "grid_maxmin": repr(bestg[0]), "grid_pt": [repr(bestg[1]), repr(bestg[2])]}

res = {}
res["A"] = analyse("A (17-digit literal cfg, certified object)", A, "centers_dec17", mp.mpf(A["R_float"]))
res["B"] = analyse("B (KKT source)", B, "centers", mp.mpf(B["R_D_mpmath"]))

W("")
W("=================== symmetry test ===================")
def rot(p, k):
    th = 2*mp.pi*k/3
    c, s = mp.cos(th), mp.sin(th)
    return (c*p[0]-s*p[1], s*p[0]+c*p[1])

for tag, cfg, key in (("A", A, "centers_dec17"), ("B", B, "centers")):
    cen = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in cfg[key]]
    W(f"-- {tag} --")
    for k in (1, 2):
        dev = [min(mp.sqrt((rot(cen[i], k)[0]-c[0])**2+(rot(cen[i], k)[1]-c[1])**2) for c in cen)
               for i in range(len(cen))]
        W(f"   rot{120*k}: max_i min_j dist = {mp.nstr(max(dev),18)}   (worst i = {dev.index(max(dev))})")
    for phi_deg in (0, 30, 60, 90, 120):
        ph = mp.pi*phi_deg/180
        c2, s2 = mp.cos(2*ph), mp.sin(2*ph)
        dev = []
        for i in range(len(cen)):
            q = (c2*cen[i][0]+s2*cen[i][1], s2*cen[i][0]-c2*cen[i][1])
            dev.append(min(mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2) for c in cen))
        W(f"   reflect(axis {phi_deg:3d}deg): max_i min_j = {mp.nstr(max(dev),18)}")
    for tol in ('1e-40', '1e-30', '1e-20', '1e-17', '1e-12'):
        cnt = 0
        for i in range(len(cen)):
            q = rot(cen[i], 1)
            if min(mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2) for c in cen) < mp.mpf(tol):
                cnt += 1
        W(f"   #i whose R120 image is within {tol}: {cnt}/12")

(EV / "struct2.txt").write_text("\n".join(OUT), encoding="utf-8")
(EV / "struct2.json").write_text(json.dumps(res, indent=2, default=str), encoding="utf-8")
print("done; lines:", len(OUT))
