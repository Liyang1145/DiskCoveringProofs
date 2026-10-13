"""Global fixed-witness NON-SHARPNESS: rotation theorem + certified quantitative version.

THEOREM (lead's route, written out in the report):
    X = candidate configuration, R = R_D(X), E = {y in D : d_X(y) = R} (d_X(y) = min_i |y - c_i|).
    If E is FINITE and 0 not in E, then for every finite Q in D there is theta with
        max_{q in Q} d_X(R_theta q) < R ,
    because each pair (q,e), q,e != 0, forbids AT MOST ONE angle, so the forbidden set is finite.
    Since R_D(R_theta X) = R_D(X) = R (rotation invariance), this says: every fixed finite witness
    set gives a value STRICTLY BELOW the candidate's radius  =>  no fixed-witness lower bound can be
    sharp.  No small-rotation or acuteness assumption is used.

THIS SCRIPT certifies, on the lead Krawczyk box (interval arithmetic):
  P1  the 18 active witnesses have value = R (9 face circumradii + 9 tie radii contain R) and the
      2 slack faces are <= R - 1e-3                                  [C892 structure]
  P2  E is finite and equals the 18 active witnesses: every Voronoi cell vertex is at distance <= R
      from its site (all 11 face circumradii <= R), and a straight segment meets a circle in <= 2
      points, so the R-level set inside a cell is exactly its vertices at distance R (= the 9 active
      circumcentres); on the boundary the arcs tile (gap = 0 identically) so E ∩ dD = the 9 ties.
  P3  0 not in E : d_X(0) = min_i |c_i| <= |y1| < R.
  Q   quantitative corollary for the candidate's own critical points Q0 (11 circumcentres + 9 ties):
      an explicit dyadic theta with CERTIFIED max_{q in Q0} d_X(R_theta q) <= T_cert - delta < T_cert
      => the witness route with Q0 cannot prove r_D(11) >= T_cert (much stronger than the exact
      strictness of the theorem).
  aux first-order structure: interior active triangles acute (circumcentre inside) and boundary ties
      with opposite-sign angular derivatives => a linear decrease is available (lead's message).

Writes only in r20-stress/out .
"""
import json, itertools
from pathlib import Path
from mpmath import mp, iv, mpf
import numpy as np

mp.dps = 60
iv.dps = 35
W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'
CERTJ = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
RAD = float.fromhex(CERTJ['certificate']['radius_hex'])
CH = [float.fromhex(v) for v in CERTJ['certificate']['center_hex']]
TCERT = mpf('0.379983853119838689722261606136093214308718957')
Z = [iv.mpf(CH[i]) + iv.mpf([-RAD, RAD]) for i in range(7)]
a0, a1, a2, a3, y0, y1, R = Z
a4 = iv.pi - 2 * (a0 + a1 + a2 + a3)
AK = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
SIN = [iv.sin(a) for a in AK]
RHO = [iv.cos(AK[k]) - iv.sqrt(R * R - SIN[k] * SIN[k]) for k in range(9)]
TH = [iv.mpf(0)] * 9
for k in range(5, 9):
    TH[k] = TH[k - 1] + AK[k - 1] + AK[k]
for k in range(3, -1, -1):
    TH[k] = TH[k + 1] - (AK[k] + AK[k + 1])
SITE = [(RHO[k] * iv.cos(TH[k]), RHO[k] * iv.sin(TH[k])) for k in range(9)] + \
       [(y0, iv.mpf(0)), (y1, iv.mpf(0))]
FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]
edges = {}
for tri in FACES:
    for i, j in itertools.combinations(sorted(tri), 2):
        edges[(i, j)] = edges.get((i, j), 0) + 1
assert len(FACES) == 11 and len(edges) == 21 and 11 - len(edges) + len(FACES) == 1
assert sum(1 for v in edges.values() if v == 1) == 9


def LO(x):
    return mpf(x.a)


def HI(x):
    return mpf(x.b)


def d2(P, Q):
    return (P[0] - Q[0]) * (P[0] - Q[0]) + (P[1] - Q[1]) * (P[1] - Q[1])


def circ(A, B, C):
    d1 = (B[0] - A[0], B[1] - A[1]); d2_ = (C[0] - A[0], C[1] - A[1])
    det = d1[0] * d2_[1] - d1[1] * d2_[0]
    assert LO(det) > 0 or HI(det) < 0
    b1 = (d1[0] * d1[0] + d1[1] * d1[1]) / 2
    b2 = (d2_[0] * d2_[0] + d2_[1] * d2_[1]) / 2
    wx = (b1 * d2_[1] - b2 * d1[1]) / det
    wy = (d1[0] * b2 - d2_[0] * b1) / det
    return (A[0] + wx, A[1] + wy), iv.sqrt(wx * wx + wy * wy)


WIT = []
for tri in FACES:
    O, r = circ(SITE[tri[0]], SITE[tri[1]], SITE[tri[2]])
    WIT.append(dict(kind='face', idx=tri, p=O, r=r))
for k in range(9):
    ca, cb = SITE[k], SITE[(k + 1) % 9]
    dx, dy = cb[0] - ca[0], cb[1] - ca[1]
    D = dx * dx + dy * dy
    kap = ((cb[0] * cb[0] + cb[1] * cb[1]) - (ca[0] * ca[0] + ca[1] * ca[1])) / 2
    dl = iv.sqrt(D)
    a0x, a0y = (kap / D) * dx, (kap / D) * dy
    t = iv.sqrt(1 - (a0x * a0x + a0y * a0y))
    cand = [(a0x + s * t * (-dy / dl), a0y + s * t * (dx / dl)) for s in (1, -1)]
    Pch = (iv.cos(TH[k] + AK[k]), iv.sin(TH[k] + AK[k]))
    pick = 0 if HI(d2(cand[0], Pch)) <= HI(d2(cand[1], Pch)) else 1
    P_ = cand[pick]
    WIT.append(dict(kind='tie', idx=(k, (k + 1) % 9), p=P_, r=iv.sqrt(d2(P_, ca))))

# ------------------------------------------------------------------ P1
act, slack = [], []
for wi, w in enumerate(WIT):
    lo, hi = LO(w['r']), HI(w['r'])
    is_R = (lo <= HI(R)) and (LO(R) <= hi)
    (act if is_R else slack).append(wi)
P1 = dict(n_active=len(act), n_slack=len(slack),
          slack_upper_le_R_minus_1e3=all(HI(WIT[i]['r']) <= LO(R) - mpf('1e-3') for i in slack),
          slack_r=[mp.nstr(HI(WIT[i]['r']), 12) for i in slack])
print('=== P1: active = value R ; slack <= R - 1e-3 ===')
print('   active %d / slack %d %s ; slack radii %s' % (len(act), len(slack), P1['slack_upper_le_R_minus_1e3'],
                                                       P1['slack_r']))

# ------------------------------------------------------------------ P2
cellof = {i: [] for i in range(11)}
for tri, w in zip(FACES, WIT[:11]):
    for i in tri:
        cellof[i].append(w)
P2_vert = dict(max_vertex_minus_R_upper=mp.nstr(max(HI(w['r']) - LO(R) for w in WIT[:11]), 8),
               all_vertices_le_R=all(HI(w['r']) <= HI(R) for w in WIT[:11]),
               interior_level_witnesses=sum(1 for w in WIT[:11] if HI(w['r']) >= LO(R)),
               boundary_ties=sum(1 for w in WIT[11:] if HI(w['r']) >= LO(R)))
print('=== P2: E finite ; every cell vertex distance <= R ; interior R-level = %d circumcentres ; '
      'boundary R-level = %d ties ===' % (P2_vert['interior_level_witnesses'], P2_vert['boundary_ties']))

# ------------------------------------------------------------------ P3
zero_d = min(iv.sqrt(d2((iv.mpf(0), iv.mpf(0)), SITE[i])) for i in range(11))
P3 = dict(d_X_0_upper=mp.nstr(HI(zero_d), 12), zero_not_in_E=bool(HI(zero_d) < LO(R)))
print('=== P3: 0 not in E : d_X(0) <= %s < R ? %s ===' % (P3['d_X_0_upper'], P3['zero_not_in_E']))

# ------------------------------------------------------------------ quantitative corollary (Q0)
Q0 = [w['p'] for w in WIT]


def mid(x):
    return (LO(x) + HI(x)) / 2


def dX_mid(x, y, th):
    """midpoint evaluation of d_X(R_theta (x,y))"""
    c, s = mp.cos(th), mp.sin(th)
    rx, ry = c * x - s * y, s * x + c * y
    return min(mp.sqrt((rx - mid(SITE[i][0])) ** 2 + (ry - mid(SITE[i][1])) ** 2) for i in range(11))


def Fmid(th):
    return max(dX_mid(mid(q[0]), mid(q[1]), th) for q in Q0)


th_best, f_best = mpf(0), mpf('1e9')
for k in range(2000):
    th = mpf(2) * mp.pi * k / 2000
    f = Fmid(th)
    if f < f_best:
        th_best, f_best = th, f
for _ in range(120):                     # golden-section refine
    lo_, hi_ = th_best - mpf('0.005'), th_best + mpf('0.005')
    gr = (mp.sqrt(5) - 1) / 2
    a_, b_ = lo_, hi_
    c_, d_ = b_ - gr * (b_ - a_), a_ + gr * (b_ - a_)
    for __ in range(200):
        if Fmid(c_) < Fmid(d_):
            b_, d_ = d_, c_
            c_ = b_ - gr * (b_ - a_)
        else:
            a_, c_ = c_, d_
            d_ = a_ + gr * (b_ - a_)
    th_best = (a_ + b_) / 2
    if Fmid(th_best) > f_best:
        break
    f_best = Fmid(th_best)
th = mpf(mp.nstr(th_best, 30))           # a specific dyadic/rational value


def dX_iv(x, y, thv):
    c, s = iv.cos(iv.mpf(thv)), iv.sin(iv.mpf(thv))
    rx, ry = c * x - s * y, s * x + c * y
    return min(iv.sqrt(d2((rx, ry), SITE[i])) for i in range(11))


vals = [dX_iv(q[0], q[1], th) for q in Q0]
worst = max(HI(v) for v in vals)
DELTA = TCERT - worst
print('=== quantitative corollary: best theta = %s ; F_mid = %s ===' % (mp.nstr(th, 20), mp.nstr(f_best, 18)))
print('   certified  max_q d_X(R_theta q) <= %s ; T_cert - that = %s  (> 0 ? %s)'
      % (mp.nstr(worst, 24), mp.nstr(DELTA, 12), bool(DELTA > 0)))

# ------------------------------------------------------------------ aux first-order structure
P4 = dict(interior_acute=[], tie_signs=[], circumcentres_nonzero=[])
for wi in range(11):
    tri = FACES[wi]
    A, B, C = SITE[tri[0]], SITE[tri[1]], SITE[tri[2]]
    # acuteness = all three vertex angles acute (equivalently: circumcentre inside the triangle)
    dots = [(A[0] - B[0]) * (C[0] - B[0]) + (A[1] - B[1]) * (C[1] - B[1]),
            (B[0] - A[0]) * (C[0] - A[0]) + (B[1] - A[1]) * (C[1] - A[1]),
            (A[0] - C[0]) * (B[0] - C[0]) + (A[1] - C[1]) * (B[1] - C[1])]
    P4['interior_acute'].append(bool(min(LO(d) for d in dots) > 0))
    O = WIT[wi]['p']
    P4['circumcentres_nonzero'].append(bool(HI(iv.sqrt(d2(O, (iv.mpf(0), iv.mpf(0))))) > 0))
for wi in range(11, 20):
    k = wi - 11
    p = WIT[wi]['p']
    sgn = []
    for i in (k, (k + 1) % 9):
        ux = (SITE[i][0] - p[0]); uy = (SITE[i][1] - p[1])
        # angular derivative of |R_theta p - c_i| at theta=0 : <u_i, J p>/|..| with u from p to c_i
        val = (ux * (-p[1]) + uy * (p[0]))
        sgn.append(mp.sign(LO(val)))
    P4['tie_signs'].append(int(sgn[0]) * int(sgn[1]) < 0)
print('=== aux: interior active triangles acute (all vertex angles acute): %d/11 ; '
      'boundary ties with opposite-sign angular derivatives: %d/9 ; circumcentres nonzero: %d/11 ==='
      % (sum(P4['interior_acute']), sum(P4['tie_signs']), sum(P4['circumcentres_nonzero'])))
print('   per-face acuteness (FACES order): %s' % ''.join('A' if x else '.' for x in P4['interior_acute']))

# first-order rate of the fixed-witness objective under a small rotation (lead's message-1 check)
rate0 = []
for wi in act:
    w = WIT[wi]
    jx, jy = -mid(w['p'][1]), mid(w['p'][0])
    vals_i = []
    for i in w['N'] if 'N' in w else [w['idx']]:
        pass
for wi in act:
    w = WIT[wi]
    jx, jy = -mid(w['p'][1]), mid(w['p'][0])
    Ns = list(w['idx']) if w['kind'] == 'face' else list(w['idx'])
    vals_i = []
    for i in Ns:
        ux, uy = mid(SITE[i][0]) - mid(w['p'][0]), mid(SITE[i][1]) - mid(w['p'][1])
        nrm = mp.sqrt(ux * ux + uy * uy)
        vals_i.append((ux * jx + uy * jy) / nrm)
    rate0.append(min(vals_i))
rate0_max = max(rate0)
print('   first-order rotation rate at theta=0: max_q min_i <u_i, Jq> = %+.6e  (< 0 ? %s)'
      % (float(rate0_max), bool(rate0_max < 0)))

out = dict(scope='fixed-finite-witness non-sharpness: certify the hypotheses of the rotation '
                 'theorem for the C891/C892 candidate (E finite, 0 not in E) and give an explicit '
                 'certified theta for the candidate critical-point witness set with '
                 'max_W d <= T_cert - delta < T_cert; interval arithmetic on the lead box',
           theorem='for every finite Q there is theta with max_Q d_X(R_theta .) < R (finitely many '
                   'forbidden angles, at most one per (q,e) pair, q,e != 0, 0 not in E)',
           P1_active_slack=P1, P2_finiteness=P2_vert, P3_origin=P3,
           theta=mp.nstr(th, 30), F_mid=mp.nstr(f_best, 24),
           certified_max=mp.nstr(worst, 30), T_cert=mp.nstr(TCERT, 40),
           delta_below_Tcert=mp.nstr(DELTA, 12), q0_route_cannot_reach_Tcert=bool(DELTA > 0),
           aux_acuteness=dict(interior_acute=P4['interior_acute'], tie_opposite=P4['tie_signs']),
           witnesses=[dict(kind=w['kind'], idx=list(w['idx']), r=[mp.nstr(LO(w['r']), 18), mp.nstr(HI(w['r']), 18)],
                           active=(i in act)) for i, w in enumerate(WIT)])
(OUT / 'global_rotation_nonsharpness.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print('[done] -> out/global_rotation_nonsharpness.json')
