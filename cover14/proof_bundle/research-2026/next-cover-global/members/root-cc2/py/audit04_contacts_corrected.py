"""root-cc2 audit step 4: CORRECTED contact/indexing audit.

Corrections to step 2/3 (kept as evidence of the mistake):
  * the free D2 family of lead/root_scout.py produces only 10 centres
    (3 orbits of 4: A=(A,B), B=(c,D), y-axis; the y-axis orbit has 2 distinct points
    and the whole family is 12 - 2 = 10).  The full 14-centre configuration keeps the
    two fixed x-axis pairs (z,0) and (s,0) from the hprec object.
  * step 3 therefore measured the covering radius of an incomplete configuration at
    (-1,0) (a reference boundary point covered by the *fixed* x-axis pair, not by the
    free family).  Recorded, superseded by this script.

Content: build the full hprec configuration, rebuild the same *physical* configuration
at the lead's new root, and compare the physical Voronoi/contact data:
  covering radius on grid + S^1 + refinement,
  the active (tight) triple set as physical point triples (not index triples),
  and whether the two objects are the same geometric configuration.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 50
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]
WS = HERE.parents[4]
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)

hp = json.loads((WS / 'research-2026/session2/type14/out/hprec_sol.json').read_text())
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z0, C0, r0 = [mp.mpf(s) for s in scout['z_c_r']]
zold = mp.mpf(hp['th'][5]); rold = mp.mpf(hp['R'])
sold = mp.sqrt(1 - rold*rold); Aold = (sold + zold)/2
told = rold + mp.sqrt(rold*rold - zold*zold)
Bold = rold + mp.sqrt(rold*rold - (Aold - zold)**2)

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

pts_old = [tuple(mp.mpf(v) for v in cc) for cc in hp['centers']]

# --- rebuild the SAME physical configuration at the new root -----------------
# hprec slot map (read off the explicit data):
#   0,1,2,3     = A-orbit      (+-0.635, +-0.454)      free  : (A,B)
#   4,5,6,7     = B-orbit      (+-0.292, +-0.842)      free  : (c,D)
#   8,9         = x-axis far   (+-0.943, 0)            fixed : (s,0)
#   10,11       = x-axis near  (+-0.327, 0)            fixed : (z,0)
#   12,13       = y-axis       (0, +-0.389)            free  : (0,t)
def build_new(z, c, r):
    s = mp.sqrt(1 - r*r); A = (s + z)/2
    t = r + mp.sqrt(r*r - z*z)
    B = r + mp.sqrt(r*r - (A - z)**2)
    D = 1 - mp.sqrt(r*r - c*c)
    return [(-A, -B), (-A, B), (A, -B), (A, B),
            (c, -D), (c, D), (-c, -D), (-c, D),
            (-s, mp.mpf(0)), (s, mp.mpf(0)),
            (z, mp.mpf(0)), (-z, mp.mpf(0)),
            (mp.mpf(0), -t), (mp.mpf(0), t)]

pts_new = build_new(z0, C0, r0)
P('slot-by-slot |Delta| between OLD (hprec) and NEW (rebuilt at lead root):')
for i in range(14):
    d = mp.sqrt((pts_old[i][0]-pts_new[i][0])**2 + (pts_old[i][1]-pts_new[i][1])**2)
    P('   %2d  old=(%s,%s)  new=(%s,%s)  |d|=%s'
      % (i, mp.nstr(pts_old[i][0], 16), mp.nstr(pts_old[i][1], 16),
         mp.nstr(pts_new[i][0], 16), mp.nstr(pts_new[i][1], 16), mp.nstr(d, 6)))

def mindist(pts, x, y):
    return min(mp.sqrt((x-a)**2 + (y-b)**2) for (a, b) in pts)

def cover_radius(pts, N=900):
    best = mp.mpf(0); arg = (mp.mpf(0), mp.mpf(0))
    h = mp.mpf(2)/N
    for i in range(N+1):
        x = -1 + i*h
        for j in range(N+1):
            y = -1 + j*h
            if x*x + y*y > 1:
                continue
            d = mindist(pts, x, y)
            if d > best:
                best, arg = d, (x, y)
    M = 4000
    for i in range(M):                       # boundary S^1
        a = 2*mp.pi*i/M
        x, y = mp.cos(a), mp.sin(a)
        d = mindist(pts, x, y)
        if d > best:
            best, arg = d, (x, y)
    x, y = arg; step = h
    for _ in range(300):
        imp = False
        for dx, dy in [(step,0),(-step,0),(0,step),(0,-step),(step,step),(-step,-step),(step,-step),(-step,step)]:
            nx, ny = x+dx, y+dy
            if nx*nx+ny*ny <= 1:
                d = mindist(pts, nx, ny)
                if d > best:
                    best, x, y, imp = d, nx, ny, True
        if not imp:
            step /= 2
            if step < mp.mpf('1e-30'):
                break
    return best, x, y

P('')
P('=' * 78)
P('covering radius R_cover = max_{|x|<=1} min_i |x-P_i|')
for name, pts in (('OLD (hprec explicit)', pts_old), ('NEW (rebuilt at lead root)', pts_new)):
    R, x, y = cover_radius(pts)
    site = min(((mp.sqrt((x-a)**2+(y-b)**2), i) for i, (a, b) in enumerate(pts)))
    P('   %-26s R_cover = %s' % (name, mp.nstr(R, 30)))
    P('   %-26s argmax  = (%s, %s)  nearest site %d' % ('', mp.nstr(x, 16), mp.nstr(y, 16), site[1]))
    P('   %-26s implied r* <= R_cover, and R_cover - r_lead = %s'
      % ('', mp.nstr(R - r0, 10)))

# --- boundary S^1: pairs of disks that meet on the circle --------------------
P('')
P('=' * 78)
P('boundary S^1 coverage: for each axis point, sites at distance ~r')
for (bx, by) in [(1, 0), (-1, 0), (0, 1), (0, -1)]:
    ds = sorted(((mp.sqrt((mp.mpf(bx)-a)**2 + (mp.mpf(by)-b)**2), i) for i, (a, b) in enumerate(pts_new)))
    P('   at (%2d,%2d): %s' % (bx, by, ', '.join('%d:%s' % (i, mp.nstr(d, 22)) for d, i in ds[:4])))

# --- tight triples as PHYSICAL triples ---------------------------------------
def tight_triples(pts, tol=mp.mpf('1e-20')):
    out = []
    for i in range(len(pts)):
        for j in range(i+1, len(pts)):
            for k in range(j+1, len(pts)):
                P1, P2, P3 = pts[i], pts[j], pts[k]
                d = 2*(P1[0]*(P2[1]-P3[1]) + P2[0]*(P3[1]-P1[1]) + P3[0]*(P1[1]-P2[1]))
                if abs(d) < mp.mpf('1e-40'):
                    continue
                ux = ((P1[0]**2+P1[1]**2)*(P2[1]-P3[1]) + (P2[0]**2+P2[1]**2)*(P3[1]-P1[1]) + (P3[0]**2+P3[1]**2)*(P1[1]-P2[1]))/d
                uy = ((P1[0]**2+P1[1]**2)*(P3[0]-P2[0]) + (P2[0]**2+P2[1]**2)*(P1[0]-P3[0]) + (P3[0]**2+P3[1]**2)*(P2[0]-P1[0]))/d
                if ux*ux + uy*uy > 1:
                    continue
                r = mp.sqrt((ux-P1[0])**2 + (uy-P1[1])**2)
                rest = min(mp.sqrt((ux-w[0])**2 + (uy-w[1])**2) for n, w in enumerate(pts) if n not in (i, j, k))
                if rest < r - mp.mpf('1e-25'):
                    continue                      # not a nearest-site vertex
                out.append((i, j, k, ux, uy, r, rest))
    return out

P('')
P('=' * 78)
P('nearest-site-filtered vertices of the FULL 14-centre configuration (|v|<1 only)')
for name, pts in (('OLD', pts_old), ('NEW', pts_new)):
    P('   --- %s' % name)
    for (i, j, k, ux, uy, r, rest) in tight_triples(pts):
        tag = 'tight' if abs(r - r0) < mp.mpf('1e-15') else 'slack'
        P('      triple %-13s r=%s  (r-lead=%s)  %s'
          % (str((i, j, k)), mp.nstr(r, 22), mp.nstr(r - r0, 6), tag))
    P('')

(OUT / 'audit04_contacts_corrected.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'audit04_contacts_corrected.txt')
