"""Step 3: exact C3-reduced structure of the n=12 candidate.

Everything here is EXACT rational (Fraction) except where explicitly labelled mp.
Central object: the 17-digit literal configuration A (certified upper-bound object).
"""
from pathlib import Path
from fractions import Fraction as F
import json, math
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
CFGA = ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json"
A = json.loads(CFGA.read_text(encoding="utf-8"))
Aq = [(F(x), F(y)) for x, y in A["centers_dec17"]]
n = 12
OUT = []
def W(s=""): OUT.append(str(s))

def d2(i, j):
    return (Aq[i][0]-Aq[j][0])**2 + (Aq[i][1]-Aq[j][1])**2

def norm2(i):
    return Aq[i][0]**2 + Aq[i][1]**2

Rlo = F("0.361102963744508672616920293903")
Rhi = F("0.361102963744508672616920293904")

# ---- D3/C3 orbit structure, verified numerically first, then reported exactly
W("### 1. C3 orbit structure of A (exact rationals)")
W(f"{'i':>3} {'|c_i|^2 (exact)':>44} {'|c_i| (~40d)':>44} {'theta_deg':>18}")
mpf = mp.mpf
for i in range(n):
    nm = norm2(i)
    r = mp.sqrt(mpf(nm.numerator)/mpf(nm.denominator))
    th = mp.atan2(mpf(str(Aq[i][1])), mpf(str(Aq[i][0])))*180/mp.pi
    W(f"{i:>3} {str(nm):>44} {mp.nstr(r,40):>44} {mp.nstr(th,18):>18}")

W()
W("### 2. squared distance matrix, 12x12 (exact, only min-3 shown per row)")
for i in range(n):
    pairs = sorted((d2(i, j), j) for j in range(n) if j != i)
    W(f"  {i:>2}: " + "   ".join(f"c{j}-> {mp.nstr(mp.sqrt(mpf(p.numerator)/mpf(p.denominator)),18)}" for p, j in pairs[:3]))

W()
W("### 3. exact tangency comparison with certified R interval")
lo2, hi2 = (2*Rlo)**2, (2*Rhi)**2
W(f"   (2R_lo)^2 = {lo2}")
W(f"   (2R_hi)^2 = {hi2}")
tangs = []
for i in range(n):
    for j in range(i+1, n):
        p = d2(i, j)
        s = "= 2R" if lo2 <= p <= hi2 else (">2R" if p > hi2 else "<2R")
        if s == "= 2R":
            tangs.append((i, j, p))
W(f"   pairs with (i,j) at distance 2R (interval-decided): {len(tangs)}")
for i, j, p in tangs:
    W(f"     ({i:2d},{j:2d})  d^2-（2Rlo)^2 = {p-lo2}")

W()
W("### 4. circumradii of ALL 220 triples, exact rational; find the ones closest to R")
rows = []
for i in range(n):
    for j in range(i+1, n):
        for k in range(j+1, n):
            a, b, c = Aq[i], Aq[j], Aq[k]
            # circumradius^2 = (|a-b|^2 |b-c|^2 |c-a|^2) / (4 * (2*Area)^2)
            lab = d2(i, j); lbc = d2(j, k); lca = d2(k, i)
            cross = 2*((b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0]))
            if cross == 0:
                continue
            rr2 = lab*lbc*lca/(cross*cross)
            rows.append((rr2, (i, j, k), lab, lbc, lca, cross))
rows.sort()
W(f"   (min over triples of |circumradius - R| ; R interval = [{float(Rlo):.20f}, {float(Rhi):.20f}])")
# compare rr to R via rr2 vs Rlo^2, Rhi^2
close = []
for rr2, tri, lab, lbc, lca, cross in rows:
    if abs(float(rr2) - float(Rhi*Rhi)) < 1e-5:
        close.append((rr2, tri, lab, lbc, lca))
W(f"   triples whose circumradius^2 is within 1e-5 of R^2: {len(close)}")
for rr2, tri, lab, lbc, lca in close:
    rr = mp.sqrt(mpf(rr2.numerator)/mpf(rr2.denominator))
    s = "r2 < R_lo^2" if rr2 < Rlo*Rlo else ("r2 > R_hi^2" if rr2 > Rhi*Rhi else "INSIDE INTERVAL")
    W(f"     tri{tri}: rr={mp.nstr(rr,32)}  rr-R_lo={mp.nstr(rr-mpf(Rlo.numerator)/mpf(Rlo.denominator),6)}"
      f"  rr^2 vs [Rlo^2,Rhi^2]: {s}")
    W(f"           side^2: {lab}, {lbc}, {lca}     (2R_lo)^2={lo2}")
    if tri in ((0,1,3),(0,6,7)):
        W(f"           side^2 - (2R_lo)^2 : {lab-lo2}, {lbc-lo2}, {lca-lo2}")
        W(f"           side^2 - (2R_hi)^2 : {lab-hi2}, {lbc-hi2}, {lca-hi2}")
W(f"   smallest triangle circumradius^2 found: {rows[0][0]} on tri{rows[0][1]}")

W()
W("### 5. incidences: which triples are exactly equilateral with side 2R (interval-decided)")
for i in range(n):
    for j in range(i+1, n):
        for k in range(j+1, n):
            ds = [d2(i, j), d2(j, k), d2(k, i)]
            if all(lo2 <= p <= hi2 for p in ds):
                W(f"   tri({i:2d},{j:2d},{k:2d}) EQUILATERAL side 2R: {[str(p) for p in ds]}")

(EV / "struct3.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
