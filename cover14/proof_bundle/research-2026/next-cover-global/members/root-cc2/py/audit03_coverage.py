"""root-cc2 audit step 3 (NUMERIC): does the new-root configuration actually cover D at r?

Adversarial check of the claim "the new root realises the covering radius r".
Independent of Voronoi enumerations: brute-force the covering radius
    R_cover(X) = max_{x in D} min_{i} |x - P_i|
on (a) a fine grid, (b) boundary S^1, (c) local refinement from the grid maxima,
for three configurations:
    NEW  = lead radical-root configuration  (z0,C0,r0 from lead/root-scout.json)
    OLD  = hprec explicit centres
    V1   = variant: only the first A-site orbit rebuilt at the new root, rest at hprec
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 50
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]
WS = HERE.parents[4]
OUT = HERE.parent / 'evidence'

hp = json.loads((WS / 'research-2026/session2/type14/out/hprec_sol.json').read_text())
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z0, C0, r0 = [mp.mpf(s) for s in scout['z_c_r']]

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

def build_lead(z, c, r):
    s = mp.sqrt(1 - r*r); A = (s + z)/2
    t = r + mp.sqrt(r*r - z*z)
    B = r + mp.sqrt(r*r - (A - z)**2)
    D = 1 - mp.sqrt(r*r - c*c)
    pts = []
    for (u, v) in [(A, B), (c, D), (0, t)]:
        for q in [(u, v), (-u, v), (u, -v), (-u, -v)]:
            if not any(abs(q[0]-w[0]) < mp.mpf('1e-40') and abs(q[1]-w[1]) < mp.mpf('1e-40') for w in pts):
                pts.append(q)
    return pts

def build_hprec():
    return [tuple(mp.mpf(v) for v in cc) for cc in hp['centers']]

def mindist(pts, x, y):
    return min(mp.sqrt((x-a)**2 + (y-b)**2) for (a, b) in pts)

def cover_radius(pts, N=1400):
    """grid over the disk |x|<=1 plus boundary S^1, then local refine on the best cells"""
    best = mp.mpf(0); bestx = None; besty = None
    # (a) square grid restricted to the disk
    h = mp.mpf(2)/N
    for i in range(N+1):
        x = -1 + i*h
        for j in range(N+1):
            y = -1 + j*h
            if x*x + y*y > 1:
                continue
            d = mindist(pts, x, y)
            if d > best:
                best, bestx, besty = d, x, y
    # (b) boundary S^1
    M = 4000
    for i in range(M):
        a = 2*mp.pi*i/M
        x, y = mp.cos(a), mp.sin(a)
        d = mindist(pts, x, y)
        if d > best:
            best, bestx, besty = d, x, y
    # (c) local refine (Nelder-Mead style simplex) from the grid argmax
    def neg(p):                       # minimise the negative min-distance
        return -mindist(pts, p[0], p[1])
    try:
        res = mp.findroot(lambda zz: [mp.diff(lambda u: neg([u, zz[1]]), zz[0]),
                                      mp.diff(lambda u: neg([zz[0], u]), zz[1])],
                          [bestx, besty]) if False else None
    except Exception:
        res = None
    # simple hill-climb refinement
    step = h
    x, y = bestx, besty
    for _ in range(200):
        improved = False
        for dx, dy in [(step, 0), (-step, 0), (0, step), (0, -step), (step, step), (-step, -step), (step, -step), (-step, step)]:
            nx, ny = x+dx, y+dy
            if nx*nx+ny*ny <= 1:
                d = mindist(pts, nx, ny)
                if d > best + mp.mpf('1e-45'):
                    best, x, y, improved = d, nx, ny, True
        if not improved:
            step /= 2
            if step < mp.mpf('1e-25'):
                break
    return best, x, y

for name, pts in (('NEW (lead radical root)', build_lead(z0, C0, r0)),
                  ('OLD (hprec centres)', build_hprec())):
    R, x, y = cover_radius(pts)
    P('%-24s  R_cover = %s' % (name, mp.nstr(R, 30)))
    P('%-24s  argmax  = (%s, %s)' % ('', mp.nstr(x, 16), mp.nstr(y, 16)))
    P('%-24s  claimed r = %s   R_cover - r = %s'
      % ('', mp.nstr(r0, 24), mp.nstr(R - r0, 8)))
    # which sites are at distance R from the argmax?
    ds = sorted(((mp.sqrt((x-a)**2+(y-b)**2), i, a, b) for i, (a, b) in enumerate(pts)))
    P('%-24s  nearest sites at argmax: %s' % ('', ', '.join('%d:%.6f' % (i, float(d)) for d, i, a, b in ds[:6])))
    P('')

# the same, but only the two A-orbits swapped in, to locate which orbit is responsible
ptsA = build_hprec()
s = mp.sqrt(1-r0*r0); A = (s+z0)/2; B = r0 + mp.sqrt(r0*r0-(A-z0)**2)
ptsV = list(ptsA)
for i in range(4):
    sx = 1 if i in (2, 3) else -1
    sy = 1 if i in (1, 3) else -1
    ptsV[i] = (sx*A, sy*B)
R, x, y = cover_radius(ptsV)
P('VARIANT: A-orbit <- new root, everything else hprec')
P('   R_cover = %s  R_cover - r = %s' % (mp.nstr(R, 30), mp.nstr(R - r0, 8)))

(OUT / 'audit03_coverage.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'audit03_coverage.txt')
