"""n=14: EXACT symmetry analysis of the high-precision source candidate.

Object: research-2026/session2/type14/out/hprec_sol.json  (14 centres, high precision;
the object certified by C411 with T = 0.33173203427623414).

Question for method selection: is the candidate exactly C2-symmetric (180 deg), and/or
mirror symmetric, and does that reduce the global problem to a bounded network?
"""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
d = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol.json").read_text(encoding="utf-8"))
C = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in d["centers"]]
n = len(C)
R = mp.mpf(d["R"])
OUT = []
def W(s=""): OUT.append(str(s))
W(f"### hprec_sol.json : n={n}  R={d['R']}")
W(f"    n_eq={d['n_eq']} dim={d['dim']} res_max={d['res_max']}")
W(f"    th_names={d['th_names']}")
W("")
W("### centres (index, coordinates, |c|, deg)")
rad = [mp.sqrt(c[0]**2+c[1]**2) for c in C]
ang = [mp.atan2(c[1], c[0])*180/mp.pi for c in C]
for i, c in enumerate(C):
    W(f"  {i:2d}: ({mp.nstr(c[0],32)}, {mp.nstr(c[1],32)})  |c|={mp.nstr(rad[i],26)}  ang={mp.nstr(ang[i],22)}")
W("")
# --- symmetry tests at high precision
W("### symmetry tests (residual = max_i min_j |g(c_i) - c_j|)")
def test(g, label):
    mx = mp.mpf(0); arg = None
    for i in range(n):
        q = g(C[i])
        dd = sorted((mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2), t) for t, c in enumerate(C))
        if dd[0][0] > mx: mx, arg = dd[0][0], (i, dd[0][1])
    W(f"  {label:<34} residual = {mp.nstr(mx,10):<20} worst i->j = {arg}")
    return mx
test(lambda p: (-p[0], -p[1]), "C2: (x,y)->(-x,-y)   [180 deg]")
test(lambda p: (-p[0], p[1]), "mirror: (x,y)->(-x,y)  [y-axis]")
test(lambda p: (p[0], -p[1]), "mirror: (x,y)->(x,-y)  [x-axis]")
test(lambda p: (p[1], p[0]), "mirror: swap x<->y")
for kk in (2, 3, 4, 6, 7):
    th = 2*mp.pi*kk/14
    cc, ss = mp.cos(th), mp.sin(th)
    test(lambda p, cc=cc, ss=ss: (cc*p[0]-ss*p[1], ss*p[0]+cc*p[1]), f"rotation {360*kk/14:.3f} deg")
W("")
# --- orbit decomposition for the symmetries that hold
W("### orbit decomposition under the symmetries that hold")
def orbits(g, tol):
    perm = []
    for i in range(n):
        q = g(C[i])
        dd = sorted((mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2), t) for t, c in enumerate(C))
        perm.append(dd[0][1])
    seen, out = set(), []
    for i in range(n):
        if i in seen: continue
        cur, o = i, []
        while cur not in seen:
            seen.add(cur); o.append(cur); cur = perm[cur]
        out.append(o)
    return perm, out
perm, orbs = orbits(lambda p: (-p[0], -p[1]), 1e-20)
W(f"  C2 permutation: {perm}")
W(f"  C2 orbits ({len(orbs)}): {orbs}")
perm2, orbs2 = orbits(lambda p: (-p[0], p[1]), 1e-20)
W(f"  mirror permutation: {perm2}")
W(f"  mirror orbits ({len(orbs2)}): {orbs2}")
W("")
# --- symmetry-reduced invariants
W("### C2-reduced invariants (7 orbits): |c|, angle, and the pair chord")
W(f"   {'orbit':<10} {'|c|':<28} {'angle_deg':<24} {'chord':<26}")
for o in orbs:
    i = o[0]
    if len(o) == 1:
        W(f"   {str(o):<10} {mp.nstr(rad[i],28):<28} {mp.nstr(ang[i],20):<24} fixed-point (must be 0)")
    else:
        j = o[1]
        ch = mp.sqrt((C[i][0]-C[j][0])**2+(C[i][1]-C[j][1])**2)
        W(f"   {str(o):<10} {mp.nstr(rad[i],28):<28} {mp.nstr(ang[i],20):<24} {mp.nstr(ch,26)}")
W("")
W("### check: is C2 exact (i.e. c_{perm[i]} == -c_i to high precision)?")
mx = mp.mpf(0)
for i in range(n):
    j = perm[i]
    dd = mp.sqrt((C[j][0]+C[i][0])**2+(C[j][1]+C[i][1])**2)
    mx = max(mx, dd)
W(f"   max_i |c_perm(i) + c_i| = {mp.nstr(mx,10)}")
W(f"   => C2 is {'EXACT (to source precision)' if mx < mp.mpf('1e-40') else 'NOT exact'}")
W("")
W("### mirror residual detail (is the mirror exact?)")
mx2 = mp.mpf(0)
for i in range(n):
    q = (-C[i][0], C[i][1])
    dd = min(mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2) for c in C)
    mx2 = max(mx2, dd)
W(f"   max_i min_j |mirror(c_i) - c_j| = {mp.nstr(mx2,10)}")
W(f"   => mirror is {'EXACT' if mx2 < mp.mpf('1e-40') else 'BROKEN (not a symmetry of the candidate)'}")
W("")
W("### boundary-active / interior split")
N = 400000
own = {}
for s in range(N):
    th = 2*mp.pi*s/N
    p = (mp.cos(th), mp.sin(th))
    ds = [mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in C]
    q = ds.index(min(ds))
    own[q] = own.get(q, 0)+1
W(f"   boundary-active ({len(own)}): {sorted(own)}")
W(f"   interior ({n-len(own)}): {sorted(set(range(n))-set(own))}")
W("")
(EV / "n14_hprec_symmetry.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
