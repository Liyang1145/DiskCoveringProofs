"""root-cc2 audit step 2 (NUMERIC): contact-structure / indexing audit.

Human-flagged question: did the contact structure really change between the old hprec
point and the new lead root?  The two points differ by ~1e-9 in r (per root-scout.json
z_c_r and hprec th), so on continuity grounds the *physical* nearest-site contact set
cannot change.  What can change is the indexing used to name sites.

Method: build both *physical* centre sets, compute the exact set of
nearest-site-filtered Voronoi vertices (circumcentre of a triple, inside D, with no
fourth site strictly closer), and report the active triples as physical point triples
(orbit class + coordinates), never as bare index triples.  Compare with the candidate
file's claim [0,4,12][1,5,13][2,6,12][3,7,13],[10,11,12],[10,11,13].

All numeric (mp.dps=60).  No certificate.
"""
import json
from itertools import combinations
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]
WS = HERE.parents[4]
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)

hp = json.loads((WS / 'research-2026/session2/type14/out/hprec_sol.json').read_text())
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z0, C0, r0 = [mp.mpf(s) for s in scout['z_c_r']]

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

# ---------------------------------------------------------------- configurations
# lead's D2 family:  boundary (active) sites, all at distance r from the free root:
#   site1 = (A,B), site2 = (C,D)                    [the A-C transverse switch]
#   site3 = (0,t)
# and the whole D2 orbit of each.
def build_lead(z, c, r):
    s = mp.sqrt(1 - r*r); A = (s + z)/2
    t = r + mp.sqrt(r*r - z*z)
    B = r + mp.sqrt(r*r - (A - z)**2)
    D = 1 - mp.sqrt(r*r - c*c)
    S = [(A, B), (c, D), (0, t)]
    pts = []
    for (u, v) in S:
        pts += [(u, v), (-u, v), (u, -v), (-u, -v)]
    seen = []
    for p in pts:                                    # de-duplicate in insertion order
        if not any(abs(p[0]-q[0]) < mp.mpf('1e-40') and abs(p[1]-q[1]) < mp.mpf('1e-40') for q in seen):
            seen.append(p)
    return seen, S

def build_hprec():
    return [tuple(mp.mpf(v) for v in cc) for cc in hp['centers']]

def voronoi_vertices(pts):
    """exact nearest-site-filtered Voronoi vertices inside D"""
    out = []
    for (i, j, k) in combinations(range(len(pts)), 3):
        Pi, Pj, Pk = pts[i], pts[j], pts[k]
        ax, ay = Pi; bx, by = Pj; cx, cy = Pk
        d = 2*(ax*(by-cy) + bx*(cy-ay) + cx*(ay-by))
        if abs(d) < mp.mpf('1e-45'):
            continue
        ux = ((ax*ax+ay*ay)*(by-cy) + (bx*bx+by*by)*(cy-ay) + (cx*cx+cy*cy)*(ay-by))/d
        uy = ((ax*ax+ay*ay)*(cx-bx) + (bx*bx+by*by)*(ax-cx) + (cx*cx+cy*cy)*(bx-ax))/d
        dp = mp.sqrt(ux*ux + uy*uy)
        if dp > 1:
            continue
        rr = mp.sqrt((ux-ax)**2 + (uy-ay)**2)
        best = min(mp.sqrt((ux-q[0])**2 + (uy-q[1])**2) for n, q in enumerate(pts) if n not in (i, j, k))
        if best < rr - mp.mpf('1e-30'):               # a fourth site strictly closer
            continue
        out.append((i, j, k, ux, uy, rr))
    return out

def classify(pts, triple, S):
    """describe a site by which family member it is"""
    labels = {}
    for n, q in enumerate(pts):
        for tag, (u, v) in zip('ABC', S):
            if abs(abs(q[0])-abs(u)) < mp.mpf('1e-25') and abs(abs(q[1])-abs(v)) < mp.mpf('1e-25'):
                sx = '+' if u > 0 and q[0] > 0 or u == 0 or (u < 0 and q[0] < 0) else '-'
                sy = '+'
                labels[n] = tag
    return ''.join(sorted(labels.get(n, '?') for n in triple))

P('=' * 78)
P('A. physical configurations')
pts_lead, S_lead = build_lead(z0, C0, r0)
pts_old = build_hprec()
P('   lead-family orbit-4 sites (|x|,|y|):  A=(%s,%s)  B=(%s,%s)  C-axis=(%s,%s)'
  % (mp.nstr(abs(S_lead[0][0]), 18), mp.nstr(abs(S_lead[0][1]), 18),
     mp.nstr(abs(S_lead[1][0]), 18), mp.nstr(abs(S_lead[1][1]), 18),
     mp.nstr(abs(S_lead[2][0]), 18), mp.nstr(abs(S_lead[2][1]), 18)))
P('   lead-family de-duplicated orbit count... len(built) = %d' % len(pts_lead))
P('   hprec explicit centre count = %d' % len(pts_old))
# cross-check: hprec orbit magnitudes
mag = sorted({(round(abs(q[0]), 12), round(abs(q[1]), 12)) for q in pts_old})
P('   hprec distinct (|x|,|y|) magnitudes: %s' % [str(m) for m in mag])

P('')
P('=' * 78)
P('B. nearest-site-filtered Voronoi vertices: NEW lead root')
for (i, j, k, ux, uy, rr) in voronoi_vertices(pts_lead):
    P('   triple %-12s  v=(%s,%s)  |v|=%s  radius=%s'
      % (str((i, j, k)), mp.nstr(ux, 16), mp.nstr(uy, 16), mp.nstr(mp.sqrt(ux*ux+uy*uy), 16), mp.nstr(rr, 20)))

P('')
P('=' * 78)
P('C. nearest-site-filtered Voronoi vertices: OLD hprec point')
for (i, j, k, ux, uy, rr) in voronoi_vertices(pts_old):
    P('   triple %-12s  v=(%s,%s)  |v|=%s  radius=%s'
      % (str((i, j, k)), mp.nstr(ux, 16), mp.nstr(uy, 16), mp.nstr(mp.sqrt(ux*ux+uy*uy), 16), mp.nstr(rr, 20)))

(OUT / 'audit02_contacts.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'audit02_contacts.txt')
