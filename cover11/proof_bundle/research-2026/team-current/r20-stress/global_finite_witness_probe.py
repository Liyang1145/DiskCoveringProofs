"""Independent route A (revised): explicit certified FIRST-ORDER descent of the fixed-witness
relaxation F(c) = max_{w in W} min_i |c_i - w| at the candidate, using the rotation direction.

Why not an LP: the first-order rate is
    D_v F = max_{w active} min_{i in N(w)} <u_i(w), v_i> ,   u_i(w) = (c_i - w)/|c_i - w|,
i.e. a max over witnesses of a MIN over the tie set: the inner "min" is a DISJUNCTION over the
nearest sites, so a single LP with per-(w,i) constraints is the wrong relaxation (it forces ALL tie
neighbours to move closer).  Instead we EXHIBIT one direction and certify its rate in interval
arithmetic:  v_i = J c_i  (the rotation of the whole configuration, J = [[0,-1],[1,0]]).
Key identity making this legal: <c_i - w, J c_i> = <c_i - w, J w> + <c_i - w, J(c_i - w)>; the last
term vanishes, so the rate of |c_i - w| under the site rotation equals the rate under rotating the
witness the other way.

Certified statement:  D_v F <= -delta < 0  with an explicit interval delta  =>  F(c* + t v) < R for
small t  =>  the fixed witness set W (11 circumcentres + 9 ties) is NOT sharp, independently of the
1-D theta-minimisation route (GLOBAL-FIXED-WITNESS-NONSHARPNESS.md, global_rotation_nonsharpness.py).

Read-only: ../lead/repaired_tc_krawczyk.json.  Writes only in r20-stress/out .
"""
import json, itertools
from pathlib import Path
from mpmath import mp, iv, mpf

mp.dps = 60
iv.dps = 35
W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'
CERTJ = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
RAD = float.fromhex(CERTJ['certificate']['radius_hex'])
CH = [float.fromhex(v) for v in CERTJ['certificate']['center_hex']]
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
ed = {}
for tri in FACES:
    for i, j in itertools.combinations(sorted(tri), 2):
        ed[(i, j)] = ed.get((i, j), 0) + 1
assert len(FACES) == 11 and len(ed) == 21 and 11 - len(ed) + len(FACES) == 1


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
    WIT.append(dict(kind='face', N=list(tri), p=O, r=r))
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
    WIT.append(dict(kind='tie', N=[k, (k + 1) % 9], p=P_, r=iv.sqrt(d2(P_, ca))))

# active set (value = R) with certified margins
act = []
for wi, w in enumerate(WIT):
    ds = [iv.sqrt(d2(w['p'], SITE[i])) for i in range(11)]
    dmin_hi = min(HI(ds[j]) for j in w['N'])
    tie = [i for i in range(11) if LO(ds[i]) <= dmin_hi + mpf('1e-9')]
    assert sorted(tie) == sorted(w['N']), (wi, tie, w['N'])
    other = [i for i in range(11) if i not in w['N']]
    sep = min(LO(ds[i]) - HI(ds[j]) for i in other for j in w['N'])
    active = all(LO(ds[j]) <= HI(R) and LO(R) <= HI(ds[j]) for j in w['N'])
    w['sep'] = sep
    w['active'] = active
    if active:
        act.append(wi)
print('witnesses: %d active of %d ; min separation to the next site = %.3e'
      % (len(act), len(WIT), float(min(w['sep'] for w in WIT))))

# ---- explicit direction v_i = J c_i ; interval rate
rate_rows = []
for wi in act:
    w = WIT[wi]
    vals = []
    for i in w['N']:
        c = SITE[i]
        ux = (c[0] - w['p'][0]) / iv.sqrt(d2(w['p'], c))
        uy = (c[1] - w['p'][1]) / iv.sqrt(d2(w['p'], c))
        vx, vy = -c[1], c[0]                      # J c_i
        vals.append(HI(ux * vx + uy * vy))
    rate_rows.append((wi, w['kind'], w['N'], min(vals)))     # per witness: MIN over its tie set
ub = max(r[3] for r in rate_rows)
lb = max(min(LO((SITE[i][0] - WIT[wi]['p'][0]) / iv.sqrt(d2(WIT[wi]['p'], SITE[i])) * (-SITE[i][1]) +
                (SITE[i][1] - WIT[wi]['p'][1]) / iv.sqrt(d2(WIT[wi]['p'], SITE[i])) * SITE[i][0])
            for i in WIT[wi]['N']) for wi in act)
print('certified  D_v F  <=  %.9e   (< 0 ? %s)   [max over witnesses of the tie-min; lower endpoint %.9e]'
      % (float(ub), bool(ub < 0), float(lb)))
worst = max(rate_rows, key=lambda r: r[3])
print('   worst witness: #%d (%s, neighbours %s) rate <= %.6e'
      % (worst[0], worst[1], worst[2], float(worst[3])))

# ---- FD control of F along v (60-digit)
def mid(x):
    return (LO(x) + HI(x)) / 2


def sites():
    return [(mid(SITE[i][0]), mid(SITE[i][1])) for i in range(11)]


def Fof(S):
    return max(min(mp.sqrt((S[i][0] - mid(w['p'][0])) ** 2 + (S[i][1] - mid(w['p'][1])) ** 2)
                   for i in w['N']) for w in WIT)


S0 = sites()
t = mpf('1e-6')
S1 = [(S0[i][0] + t * (-S0[i][1]), S0[i][1] + t * S0[i][0]) for i in range(11)]
print('   FD control: F(c*) = %s ; F(c* + t v) = %s ; slope = %+.6e'
      % (mp.nstr(Fof(S0), 18), mp.nstr(Fof(S1), 18), float((Fof(S1) - Fof(S0)) / t)))

out = dict(scope='explicit certified first-order descent of the fixed-witness relaxation at the '
                 'candidate along the rotation direction v_i = J c_i; interval rate; independent of '
                 'the 1-D theta route; conditional on the lead box only',
           n_active=len(act), certificate_rate_upper=mp.nstr(ub, 24), negative=bool(ub < 0),
           rate_lower_endpoint=mp.nstr(lb, 24), FD_slope=float((Fof(S1) - Fof(S0)) / t),
           per_witness=[[r[0], r[1], r[2], mp.nstr(r[3], 18)] for r in rate_rows])
(OUT / 'global_finite_witness_probe.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print('[done] -> out/global_finite_witness_probe.json')
