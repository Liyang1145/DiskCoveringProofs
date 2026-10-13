"""Convention check: what exactly does 'R_D(C)' mean in this workspace's pipeline?

Read the actual definition from research-2026/session2/n1314/py/rd.py and cert_bb.py and
test it numerically on this config with an independent method (Welzl min enclosing circle
of the *complement* direction -- i.e. the standard deep-hole computation).
"""
from pathlib import Path
import re, json, math
import mpmath as mp
mp.mp.dps = 40
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
OUT = []
def W(s=""): OUT.append(str(s))
for f in ("rd.py", "cert_bb.py"):
    t = (ROOT / "research-2026/session2/n1314/py" / f).read_text(encoding="utf-8")
    W(f"===== {f} (first 30 lines) =====")
    W("\n".join(t.splitlines()[:30]))
    W("")

A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
cen = [(float(x), float(y)) for x, y in A["centers_dec17"]]
# independent check: R_D = max_{x in D} min_i |x-c_i|
# (a) Voronoi vertices inside D  (b) boundary local maxima
import itertools
best = (-1, None, None)
for i, j, k in itertools.combinations(range(len(cen)), 3):
    ax, ay = cen[i]; bx, by = cen[j]; cx, cy = cen[k]
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < 1e-15: continue
    ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den
    uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den
    if ux*ux+uy*uy > 1: continue
    d = min(math.dist((ux, uy), c) for c in cen)
    if d > best[0]: best = (d, (ux, uy), (i, j, k))
W(f"independent R_D (Voronoi vertices only) = {best[0]!r}  at {best[1]}  tri{best[2]}")
# boundary
bb = (-1, None)
for t in range(200000):
    th = 2*math.pi*t/200000
    p = (math.cos(th), math.sin(th))
    d = min(math.dist(p, c) for c in cen)
    if d > bb[0]: bb = (d, th)
W(f"independent boundary max-min = {bb[0]!r} at theta={bb[1]*180/math.pi:.8f}")
W(f"=> R_D(C) = max({best[0]!r}, {bb[0]!r}) = {max(best[0], bb[0])!r}")
W(f"   certified D2 interval = [0.3611029637445086726169202939, 0.36110296374450867261692029394]")
W("")
W(f"cf. 1 - |c_0| = {1 - math.hypot(*cen[0]):.17g};   |c0| = {math.hypot(*cen[0]):.17g}")
W(f"    |c_6| = {math.hypot(*cen[6]):.17g};  |c0|+|c6| = {math.hypot(*cen[0])+math.hypot(*cen[6]):.17g}")
W(f"    |c_3| = {math.hypot(*cen[3]):.17g}")
W(f"    R_D + |c0| = {max(best[0], bb[0]) + math.hypot(*cen[0]):.17g}")
(ROOT / "research-2026/n12-global/members/candidate/evidence/convention.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
