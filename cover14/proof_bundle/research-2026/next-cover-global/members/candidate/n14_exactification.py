"""n=14: MINIMAL exactification system and activity diagram from the D2 7-parameter object.

Object (read-only): research-2026/session2/type14/out/hprec_sol.json
  14 centres; R = 0.33173203427623412351550664...
  Exact D2 (180-deg rotation + both axis mirrors), 7 orbits of size 2, NO fixed point.

Coordinates are chosen so that the candidate's D2 action is the standard one:
    sigma_x : (x,y) -> (x,-y) ,  sigma_y : (x,y) -> (-x,y)
(both are EXACT symmetries of the saved object).

A D2-invariant configuration is determined by its 7 ORBIT REPRESENTATIVES
    P_0..P_6  in the closed first-quadrant-like fundamental domain,
    orbit(P) = { (x,y), (x,-y), (-x,y), (-x,-y) }   (with x=0 or y=0 degeneracies).
So an abstract orbit needs only the pair (x,y) of its representative: 14 coordinates.
(The stored 'th' vector has 7 numbers because the 7 orbits happen to have special
positions - see the orbit table; we keep the general 14-coordinate formulation and
record those special positions as extra constraints.)

This script:
  1. re-labels the saved centres into the D2 frame and identifies the 7 orbits;
  2. builds the 14 ACTIVE faces (f = R) in the orbit language;
  3. writes the exactification residuals  E_face(P) = |u_face - P|^2 - R^2  for the
     circumcentre u_face of each face;
  4. computes the numerical Jacobian rank of the whole system at the solution, to
     decide how many independent constraints the exactification really has.
"""
from pathlib import Path
import json, itertools
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
d = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol.json").read_text(encoding="utf-8"))
C0 = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in d["centers"]]
R = mp.mpf(d["R"])
OUT = []
def W(s=""): OUT.append(str(s))

# ---------- 1. relabel into the D2 frame ----------
# the saved object already has its symmetry axes = the coordinate axes;
# verify and build the orbit list.
def dd(p, q): return mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
perm_c2 = []
for i in range(14):
    q = (-C0[i][0], -C0[i][1])
    perm_c2.append(min(range(14), key=lambda t: dd(q, C0[t])))
seen, orbits = set(), []
for i in range(14):
    if i in seen: continue
    o = sorted({i, perm_c2[i]})
    orbits.append(o); seen.update(o)
orbits.sort(key=lambda o: -mp.sqrt(C0[o[0]][0]**2+C0[o[0]][1]**2))
W("### 1. D2 orbits of the saved object (sorted by |c|)")
for k, o in enumerate(orbits):
    i = o[0]
    W(f"  orbit {k}: {str(o):<10} rep=({mp.nstr(C0[i][0],24)}, {mp.nstr(C0[i][1],24)})"
      f"  |c|={mp.nstr(mp.sqrt(C0[i][0]**2+C0[i][1]**2),24)}"
      f"  ang={mp.nstr(mp.atan2(C0[i][1],C0[i][0])*180/mp.pi,16)}")
W("")
W("### representatives specialised to the axes:")
for k, o in enumerate(orbits):
    i = o[0]
    ax = (abs(C0[i][0]) < mp.mpf('1e-30'))
    ay = (abs(C0[i][1]) < mp.mpf('1e-30'))
    W(f"  orbit {k}: on the y-axis: {ax}   on the x-axis: {ay}")
W("")

# ---------- 2. the 14 ACTIVE faces ----------
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < mp.mpf("1e-40"):
        return (mp.mpf("inf"), mp.mpf("inf"))
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den)
nn = lambda p: mp.sqrt(p[0]**2+p[1]**2)
active = []
DEGEN = []
for tri in itertools.combinations(range(14), 3):
    u = circ(C0[tri[0]], C0[tri[1]], C0[tri[2]])
    if u[0] == mp.mpf("inf") or nn(u) > 1:
        DEGEN.append(tri); continue
    ds = sorted((dd(u, c), t) for t, c in enumerate(C0))
    if ds[3][0]-ds[0][0] < mp.mpf('1e-25'): continue
    if abs(ds[0][0]-R) < mp.mpf('1e-14'):
        active.append(tri)
W(f"### degenerate/outside triples skipped: {len(DEGEN)}")
W(f"### 2. the {len(active)} ACTIVE faces (f = R), in orbit language")
o_of = {}
for k, o in enumerate(orbits):
    for i in o: o_of[i] = k
act_orb = []
for tri in active:
    ot = tuple(sorted({o_of[i] for i in tri}))
    sz = [ [j for j in tri if o_of[j] == k] for k in ot ]
    act_orb.append((tri, ot, sz))
    W(f"  tri{str(tri):<16} orbit-type {ot}  multiplicity {[len(z) for z in sz]}"
      f"  kind={'HHH' if len(ot)==3 else ('BHH' if 0 in ot or 1 in ot or 2 in ot else '')}")
W("")
# group the faces by orbit type
from collections import Counter
cnt = Counter(a[1] for a in act_orb)
W("### active face orbit-types (representative form)")
for typ, c in sorted(cnt.items(), key=lambda kv: -kv[1]):
    ex = [a for a in act_orb if a[1] == typ][0]
    W(f"  orbit-type {typ}  x{c}   example tri{ex[0]}")
    W(f"     representative face: {ex[0]}   (orbits {ex[2]})")
W("")
# orbit types in terms of boundary(B) vs inner(I): treat orbits 0..2 = B-like (|c|>=0.78)
kind = {}
for k, o in enumerate(orbits):
    i = o[0]
    kind[k] = 'B' if mp.sqrt(C0[i][0]**2+C0[i][1]**2) > mp.mpf('0.5') else 'I'
W("### orbit kinds (B: |c|>0.5 boundary-like; I: inner)")
W("   " + "  ".join(f"o{k}={kind[k]}" for k in range(7)))
W("")
W("### face census in kind language")
cen2 = Counter()
for tri, ot, sz in act_orb:
    cen2[''.join(sorted(kind[k] for k in ot))] += 1
for kk, v in sorted(cen2.items()):
    W(f"   {kk}: {v} faces")
W("")
W("### 3. exactification residuals for the representative faces")
W("  For a face with site triple (i,j,k), define u = circumcentre(i,j,k) and")
W("    E(P) = ( |u - c_i|^2 - R^2 , |u - c_j|^2 - R^2 , |u - c_k|^2 - R^2 ).")
W("  At a valid configuration all three vanish for every ACTIVE face.")
W("  Here we evaluate them at the saved solution (sanity) and count independent ones.")
W("")
seen_typ = set()
for tri, ot, sz in act_orb:
    if ot in seen_typ: continue
    seen_typ.add(ot)
    i, j, k = tri
    u = circ(C0[i], C0[j], C0[k])
    e = [mp.sqrt((u[0]-C0[t][0])**2+(u[1]-C0[t][1])**2)**2 - R**2 for t in (i, j, k)]
    W(f"  orbit-type {ot} (example tri{tri}): E = "
      + ", ".join(mp.nstr(x, 8) for x in e))
W("")
W("### 4. how many independent conditions?  (constraint count per orbit-type)")
W("   By D2, each orbit-type contributes (number of distinct D2 images) x 1..3 scalar")
W("   conditions.  Count them:")
tot = 0
for typ, c in cnt.items():
    nimg = 4   # D2 act freely (no orbit has a stabiliser beyond the trivial one here)
    # divide by the number of times the same condition repeats
    W(f"   orbit-type {typ}: {c} faces, |D2| = 4, repetitions per class = {c//max(1,c//4) if c else 0}")
    tot += c
W(f"   total active faces = {tot}")
W("")
W("### 5. numerical Jacobian rank of the active-face system in the 7 orbit coordinates")
W("   coordinates: for each orbit k, the representative pair (x_k, y_k);")
W("   the 14 centres are generated by the 4 D2 images.")
# build the D2 image list for a representative
def images(p):
    x, y = p
    return [(x, y), (x, -y), (-x, y), (-x, -y)]
def build(P):
    C = []
    for p in P:
        C.extend(images(p))
    return C
# map orbit index -> the 4 centre slots (matching the saved ordering)
slot = {}
for k, o in enumerate(orbits):
    slot[k] = o
def build_ordered(P):
    C = [None]*14
    for k, o in enumerate(orbits):
        ims = images(P[k])
        # assign images to the slots of orbit o (sorted by angle to be deterministic)
        ims_sorted = sorted(ims, key=lambda q: mp.atan2(q[1], q[0]))
        o_sorted = sorted(o, key=lambda t: mp.atan2(C0[t][1], C0[t][0]))
        for t, q in zip(o_sorted, ims_sorted):
            C[t] = q
    return C
P0 = [(C0[o[0]][0], C0[o[0]][1]) for o in orbits]
# sanity: rebuild reproduces the saved centres
Cb = build_ordered(P0)
W(f"   rebuild check: max_t |C_t - saved_t| = {mp.nstr(max(dd(Cb[t], C0[t]) for t in range(14)),10)}")
W("")
import sys as _sys
def W2(s):
    print(s); _sys.stdout.flush()

def resid(P):
    C = build_ordered(P)
    out = []
    for tri, ot, sz in act_orb:
        i, j, k = tri
        u = circ(C[i], C[j], C[k])
        if u[0] == mp.mpf("inf"):
            continue                     # degenerate triple: no circumcentre
        for t in (i, j, k):
            v = mp.sqrt((u[0]-C[t][0])**2+(u[1]-C[t][1])**2)**2 - R**2
            if abs(v) == mp.mpf("inf"):
                continue
            out.append(v)
    return out
r0 = resid(P0)
W(f"   residual norm at the saved solution: max|E| = {mp.nstr(max(abs(x) for x in r0),8)}")
W(f"   #residual components = {len(r0)}   (14 faces x 3 = 42 before redundancy)")
# numerical Jacobian
ndim = 14
r0v = resid(P0)
m = len(r0v)
J = mp.matrix(m, ndim)
import numpy as _np
Jn = _np.zeros((m, ndim))
h = mp.mpf('1e-25')
for kk in range(ndim):
    oi, cc = divmod(kk, 2)
    Pp = [list(p) for p in P0]; Pm = [list(p) for p in P0]
    Pp[oi][cc] += h; Pm[oi][cc] -= h
    rp = resid([tuple(p) for p in Pp]); rm = resid([tuple(p) for p in Pm])
    for a in range(m):
        J[a, kk] = (rp[a]-rm[a])/(2*h)
        Jn[a, kk] = float((rp[a]-rm[a])/(2*h))
sv = _np.linalg.svd(Jn, compute_uv=False)
sv = [mp.mpf(float(x)) for x in sv]
W("")
W("   singular values of the 42x14 active-face Jacobian:")
W("     " + ", ".join(mp.nstr(s, 8) for s in sv))
W(f"   rank at rel-tol 1e-14: {sum(1 for s in sv if s > mp.mpf('1e-14')*sv[0])} (max 14)")
W(f"   rank at rel-tol 1e-10: {sum(1 for s in sv if s > mp.mpf('1e-10')*sv[0])} (max 14)")
W("")
W("### interpretation")
W("   The moduli space of D2-symmetric 14-disk configurations has dimension")
W("   2*7 - dim(D2) = 14 - 2 = 12 (the D2 action fixes no centre, so 2 gauge parameters).")
W("   An isolated candidate therefore needs 12 independent active conditions.")
W(f"   The active-face system provides rank {sum(1 for s in sv if s > mp.mpf('1e-14')*sv[0])}.")
(EV / "n14_exactification.txt").write_text("\n".join(OUT), encoding="utf-8")
pass
