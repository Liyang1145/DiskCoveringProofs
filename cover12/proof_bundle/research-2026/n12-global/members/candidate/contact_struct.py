"""Step 2: full contact / active-set / nearest-centre-switching extraction.

Exact rational where the arithmetic allows it (pairwise distances, tangency tests);
mpmath dps=60 for circle/Voronoi quantities (labelled).

Inputs read-only:
  A = research-2026/session2/n1314/cfg/cert_n12_othern.json       (17-digit literal, certified object)
  B = flash-n11/members/othern-scout/s3/n12_d3_kkt.json           (KKT source, 48-58 digit literals)
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
RA = mp.mpf(A["R_float"])
RB = mp.mpf(B["R_D_mpmath"])

def load(cfg, key, R):
    cen = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in cfg[key]]
    return cen, R

def report(tag, cfg, key, R):
    cen, R = load(cfg, key, R)
    n = len(cen)
    lines = []
    W = lines.append
    W(f"############ {tag}: n={n}, R={mp.nstr(R,30)} ############")
    # radii from origin
    W("[radii/angles]")
    for i, c in enumerate(cen):
        rho = mp.sqrt(c[0]**2 + c[1]**2)
        th = mp.atan2(c[1], c[0])
        W(f"  i={i:2d} rho={mp.nstr(rho,28)}  rho-R={mp.nstr(rho-R,20):>26}  "
          f"rho-2R={mp.nstr(rho-2*R,20):>26}  (1-R)-rho={mp.nstr((1-R)-rho,20):>26} "
          f" theta_deg={mp.nstr(th*180/mp.pi,24)}")
    # pairwise distances vs 2R and vs sums
    W("[pair distance table: only |d-2R|<1e-8 or |d-(rho_i+rho_j)|<1e-8]")
    rad = [mp.sqrt(c[0]**2+c[1]**2) for c in cen]
    pairs_nearest = {i: None for i in range(n)}
    for i in range(n):
        for j in range(i+1, n):
            d = mp.sqrt((cen[i][0]-cen[j][0])**2 + (cen[i][1]-cen[j][1])**2)
            note = []
            if mp.fabs(d - 2*R) < 1e-12: note.append("d=2R(TANGENT)")
            if mp.fabs(d - (rad[i]+rad[j])) < 1e-12: note.append("d=r_i+r_j")
            if note:
                W(f"  ({i:2d},{j:2d}) d={mp.nstr(d,30)}  d-2R={mp.nstr(d-2*R,6)}  "
                  f"d-(ri+rj)={mp.nstr(d-(rad[i]+rad[j]),6)}  {' '.join(note)}")
    # exact rational tangency tests for A
    W("[exact-rational tangency tests (squared distances vs (2R)^2)]")
    if tag == "A":
        qA = [(F(x), F(y)) for x, y in cfg[key]]
        # certified R interval from d2 replay
        Rlo, Rhi = F("0.361102963744508672616920293903"), F("0.361102963744508672616920293904")
        for i in range(n):
            for j in range(i+1, n):
                d2 = (qA[i][0]-qA[j][0])**2 + (qA[i][1]-qA[j][1])**2
                tlo, thi = (2*Rlo)**2, (2*Rhi)**2
                if abs(float(d2) - float(tlo)) < 1e-6:
                    W(f"  ({i:2d},{j:2d}) d2_exact={d2}")
                    W(f"        d2-(2Rlo)^2={d2-tlo}   sign={'EQUALS-IT' if d2==tlo else ('>' if d2>tlo else '<')}")
                    W(f"        d2-(2Rhi)^2={d2-thi}   (d2-2Rlo^2 is exact Fraction; magnitude "
                      f"{float(abs(d2-tlo)):.3e})")
    # --- Voronoi / Delaunay on the interior: circumcentres of degenerate triples
    W("[near-degenerate triples: circumradius ~ R or all three pair distances ~2R]")
    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                ax, ay = cen[i]; bx, by = cen[j]; cx, cy = cen[k]
                d = 2*((ax-cx)*(by-cy) - (ay-cy)*(bx-cx))
                if mp.fabs(d) < mp.mpf('1e-40'): continue
                ux = ((ax**2+ay**2-cx**2-cy**2)*(by-cy) - (ay-cy)*(bx**2+by**2-cx**2-cy**2))/d
                uy = ((ax-cx)*(bx**2+by**2-cx**2-cy**2) - (ax**2+ay**2-cx**2-cy**2)*(bx-cx))/d
                rr = mp.sqrt((ux-ax)**2 + (uy-ay)**2)
                dd = [mp.sqrt((ux-cen[t][0])**2 + (uy-cen[t][1])**2) for t in range(n)]
                dmin = min(dd)
                if mp.fabs(rr-R) < 1e-9:
                    onb = mp.sqrt(ux**2+uy**2)
                    W(f"  tri({i:2d},{j:2d},{k:2d}) circumcentre=({mp.nstr(ux,22)},{mp.nstr(uy,22)}) "
                      f"rr={mp.nstr(rr,30)} rr-R={mp.nstr(rr-R,6)} |u|={mp.nstr(onb,20)} "
                      f"insideD={onb < 1} min-to-other={mp.nstr(dmin,20)}")
    # --- 3-wise intersection maxima: points at distance exactly R from three centres
    W("[triples whose three R-circles have a common point (intersection of 3 circumferences of radius R)]")
    cnt = 0
    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                ax, ay = cen[i]; bx, by = cen[j]; cx, cy = cen[k]
                d = 2*((ax-cx)*(by-cy) - (ay-cy)*(bx-cx))
                if mp.fabs(d) < mp.mpf('1e-40'): continue
                # circumcentre u, circumradius rr; points at distance R from all three exist iff rr<=R
                ux = ((ax**2+ay**2-cx**2-cy**2)*(by-cy) - (ay-cy)*(bx**2+by**2-cx**2-cy**2))/d
                uy = ((ax-cx)*(bx**2+by**2-cx**2-cy**2) - (ax**2+ay**2-cx**2-cy**2)*(bx-cx))/d
                rr = mp.sqrt((ux-ax)**2 + (uy-ay)**2)
                if rr <= R*(1+mp.mpf('1e-30')):
                    # the two common points
                    h = mp.sqrt(max(R*R - rr*rr, mp.mpf(0)))
                    vx, vy = (cx-ax), (cy-ay)
                    L = mp.sqrt(vx**2+vy**2)
                    # direction perpendicular to (u - a) normalised, mapped
                    e1 = ((bx-ax)/mp.sqrt((bx-ax)**2+(by-ay)**2), (by-ay)/mp.sqrt((bx-ax)**2+(by-ay)**2))
                    e2 = (ux-ax, uy-ay)
                    L2 = mp.sqrt(e2[0]**2+e2[1]**2)
                    if L2 == 0: continue
                    e2 = (e2[0]/L2, e2[1]/L2)
                    p1 = (ux + h*e2[0], uy + h*e2[1])
                    p2 = (ux - h*e2[0], uy - h*e2[1])
                    for p in (p1, p2):
                        onb = mp.sqrt(p[0]**2+p[1]**2)
                        if onb <= 1:
                            dd = [mp.sqrt((p[0]-cen[t][0])**2 + (p[1]-cen[t][1])**2) for t in range(n)]
                            mn = min(dd)
                            W(f"  tri({i:2d},{j:2d},{k:2d}) p=({mp.nstr(p[0],20)},{mp.nstr(p[1],20)}) "
                              f"|p|={mp.nstr(onb,18)} min-other-dist={mp.nstr(mn,20)} "
                              f"nn={dd.index(mn)}  (is max-cover point: {mp.fabs(mn-R)<1e-20})")
                            cnt += 1
    W(f"  -> {cnt} candidate triple points inside D")
    return "\n".join(lines)

txt = []
txt.append(report("A (17-digit literal certified cfg)", A, "centers_dec17", RA))
txt.append("")
txt.append(report("B (KKT source)", B, "centers", RB))
(EV / "contact_struct.txt").write_text("\n".join(txt), encoding="utf-8")
print("\n".join(txt))
