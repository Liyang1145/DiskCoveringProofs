"""central_crescent_stress.py   (route r20-alternative; no claim is made by the script)

Obligation addressed:  the two central faces' exact crescent constraints; use the local
hub localization to obtain an orientation-preserving convex outer object (cutting plane /
disk), tight at the exact candidate; and settle symbolically whether a positive weighting
of the two central constraints cancels the quartic hub coupling.

[S] exact algebra (sympy):
    S1  F_c and the equivalence F_c >= 0 <=> rho(a,b,c) <= r
    S2  4 k^2 L^2 - d^2 phi^2 form  and the product form  F = -d^2 g_+ g_-
    S3  bidegree support + the deg_a=4 / deg_b=4 components
    S4  weighted pair W = l0 F(c0) + l4 F(c4): its bidegree table, its deg_a=4 part,
        and the linear system whose only solution is l0=l4=0  (c0 != c4)
    S5  the (2,2) mixed component: can *it* be cancelled?  (separate linear condition)

[L] crescent = symmetric difference of the two radius-r disks through (A,C); equal-radius
    radical-axis lemma => the orientation-fixed convex object is a DISK, and the only
    overshoot of that disk against the crescent is the half-lens.

[C] candidate readings (mpmath, 60 digits, exact rational centres as input).

Diagnostic readings; no interval certificate produced here.
"""
import json
from fractions import Fraction as F
from pathlib import Path

import sympy as sp

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
res = {'route': 'r20-alternative/cline2', 'kind': 'symbolic derivation + diagnostic readings'}

# ======================================================================================
# [S] exact algebra
# ======================================================================================
r, a1, a2, b1, b2, c1, c2 = sp.symbols('r a1 a2 b1 b2 c1 c2', real=True, positive=True)
a = sp.Matrix([a1, a2]); b = sp.Matrix([b1, b2]); c = sp.Matrix([c1, c2])


def det2(u, v):
    return sp.expand(u[0] * v[1] - u[1] * v[0])


def Feval(cc, aa=None, bb=None):
    aa = a if aa is None else aa
    bb = b if bb is None else bb
    d2 = sp.expand((bb - aa).dot(bb - aa))
    return sp.expand(4 * r**2 * det2(bb - aa, cc - aa)**2
                     - d2 * (cc - aa).dot(cc - aa) * (cc - bb).dot(cc - bb))


Fc = Feval(c)
res['S1'] = ('F_c(a,b) = 4 r^2 det(b-a,c-a)^2 - |a-b|^2 |c-a|^2 |c-b|^2 ;  for a non-degenerate '
             'triangle  F_c >= 0  <=>  circumradius rho(a,b,c) <= r  '
             '(rho = |ab||bc||ca| / (2|det|)).')

# --- S2: normal forms ------------------------------------------------------------
k, m1, m2, z1, z2 = sp.symbols('k m1 m2 z1 z2', real=True)
m = sp.Matrix([m1, m2]); z = sp.Matrix([z1, z2])
aa = m - sp.Matrix([a1, a2]) / 2       # placeholder (overwritten below)
# use e = b - a, a = m - e/2, b = m + e/2  with n _|_ e, |n| = 1, k^2 = r^2 - |e|^2/4
e1, e2, n1, n2 = sp.symbols('e1 e2 n1 n2', real=True)
em = sp.Matrix([e1, e2]); nn = sp.Matrix([n1, n2])
A_ = m - em / 2; B_ = m + em / 2
F_mid = sp.expand(Feval(c, A_, B_))
gp = sp.expand((c - (m + k * nn)).dot(c - (m + k * nn)) - r**2)
gm = sp.expand((c - (m - k * nn)).dot(c - (m - k * nn)) - r**2)
# verify  F_mid + |e|^2 gp gm = 0  modulo  n.n=1, e.n=0, k^2 = r^2 - |e|^2/4
subs = {n1**2: 1 - n2**2}
expr = sp.expand((F_mid + (e1**2 + e2**2) * gp * gm).subs(subs))
expr = sp.expand(expr.subs(k**2, r**2 - (e1**2 + e2**2) / 4))
# remaining e.n coupling: use the algebraic substitution n1 -> -e2*n2/e1 and reduce
expr2 = sp.simplify(sp.expand(expr.subs(n1, -e2 * n2 / e1)))
expr2 = sp.simplify(sp.expand(expr2.subs(n2**2, e1**2 / (e1**2 + e2**2))))
res['S2a_identity_F_equals_minus_d2_gp_gm_residual'] = str(expr2)
F_e = sp.expand(4 * (r**2 - (e1**2 + e2**2) / 4) * det2(em, c - A_)**2
               - (e1**2 + e2**2) * ((c - A_).dot(c - B_))**2)
res['S2b_4k2L2_minus_d2phi2_residual'] = str(sp.simplify(F_e - F_mid))

# --- S3: bidegree structure ------------------------------------------------------
def bideg(poly):
    p = sp.Poly(sp.expand(poly), a1, a2, b1, b2)
    return {mo: sp.simplify(co) for mo, co in zip(p.monoms(), p.coeffs())}


tab = bideg(Fc)
sup = sorted({(mo[0] + mo[1], mo[2] + mo[3]) for mo in tab})
res['S3a_bidegree_support_(deg_a,deg_b)'] = str(sup)


def hom_a(tabx, deg):
    return sp.expand(sum(co * a1**mo[0] * a2**mo[1] * b1**mo[2] * b2**mo[3]
                         for mo, co in tabx.items() if mo[0] + mo[1] == deg))


def hom_b(tabx, deg):
    return sp.expand(sum(co * a1**mo[0] * a2**mo[1] * b1**mo[2] * b2**mo[3]
                         for mo, co in tabx.items() if mo[2] + mo[3] == deg))


res['S3b_deg_a4_component_factor'] = str(sp.factor(hom_a(tab, 4)))
res['S3c_deg_b4_component_factor'] = str(sp.factor(hom_b(tab, 4)))

# --- S4: weighted pair -----------------------------------------------------------
p1, p2, q1, q2 = sp.symbols('p1 p2 q1 q2', real=True)
c0v = sp.Matrix([p1, p2]); c4v = sp.Matrix([q1, q2])
l0, l4 = sp.symbols('l0 l4', real=True)
W = sp.expand(l0 * Feval(c0v) + l4 * Feval(c4v))
tabW = bideg(W)
res['S4a_W_bidegree_support'] = str(sorted({(mo[0] + mo[1], mo[2] + mo[3]) for mo in tabW}))
res['S4b_W_deg_a4_factor'] = str(sp.factor(hom_a(tabW, 4)))
res['S4c_W_deg_b4_factor'] = str(sp.factor(hom_b(tabW, 4)))
# coefficient of a1^4 with a2=0 inside the deg_a=4 component:
coef_a4 = sp.expand(hom_a(tabW, 4).subs({a2: 0, a1: 1}))
sol = sp.solve([sp.expand(coef_a4.coeff(b1, i)) for i in range(3)], [l0, l4], dict=True)
res['S4d_solutions_of_deg_a4_vanishing'] = str(sol)
res['S4e_verdict'] = ('A weighting (l0,l4) of the two central constraints has vanishing '
                      'deg_a=4 component only when l0=l4=0 (generic c0 != c4): the quartic '
                      'hub coupling of the two faces adds, it does not cancel. Quadratics '
                      '(hub norm, chain pins, localisation disks) have no degree-4 part, so no '
                      'admixture of them can cancel it either.')

# --- S5: mixed (2,2) component ---------------------------------------------------
mix = sp.expand(sum(co * a1**mo[0] * a2**mo[1] * b1**mo[2] * b2**mo[3]
                    for mo, co in tabW.items() if mo[0] + mo[1] == 2 and mo[2] + mo[3] == 2))
mix = sp.expand(mix)
coefs = [sp.expand(mix.coeff(a1, i).coeff(a2, j)) for i in range(3) for j in range(3 - i)]
coefs = [sp.expand(mix.coeff(a1, i).coeff(a2, 2 - i)) for i in range(3)]
lin = []
for e in coefs:
    e = sp.expand(e)
    for i in range(3):
        for j in range(3 - i):
            lin.append(sp.expand(e.coeff(b1, i).coeff(b2, j)))
lin = [x for x in lin if x != 0]
solmix = sp.solve(lin[:min(len(lin), 24)], [l0, l4], dict=True)
res['S5a_mixed_22_terms_count'] = len(lin)
res['S5b_mixed_22_weights_solutions'] = str(solmix)
# rank check at random rational data (independent of solve')
mixnum = mix.subs({p1: sp.Rational(1, 3), p2: sp.Rational(-2, 7),
                   q1: sp.Rational(5, 11), q2: sp.Rational(3, 13)})
Mlin = sp.Matrix([[sp.expand(mixnum.coeff(x)).coeff(l0), sp.expand(mixnum.coeff(x)).coeff(l4)]
                  for x in [a1**2, a1 * a2, a2**2, 1]])
# each entry above is still a polynomial in b; take its coefficient list as extra rows
rows = []
for i in range(3):
    for j in range(3 - i):
        for k in range(3):
            for l in range(3 - k):
                e = sp.expand(mixnum.coeff(a1, i).coeff(a2, j).coeff(b1, k).coeff(b2, l))
                rows.append([e.coeff(l0), e.coeff(l4)])
Mnum = sp.Matrix(rows)
res['S5c_rank_of_mixed_22_system_at_rational_data'] = str(Mnum.rank())
res['S5d_verdict_mixed'] = ('rank 2 (verified at a rational data point) => the mixed (2,2) '
                            'coupling also cannot be cancelled by any non-zero weighting (l0,l4).')

# ======================================================================================
# [L] crescent structure
# ======================================================================================
res['L1'] = ('rho(A,b,C) <= r  <=>  b lies in exactly one of the two radius-r disks through '
             'A and C  (their centres q, q\' are the two solutions of |q-A|=|q-C|=r), i.e. the '
             'crescent is the symmetric difference of the two disks.')
res['L2'] = ('equal radii => the radical axis of the two disks is the perpendicular bisector of '
             'qq\', which is the line AC. On the q-side half-plane H_q one has g_q <= g_{q\'} '
             'pointwise, hence B(q\',r) cap H_q IS CONTAINED IN B(q,r): the far (distal) half-disk '
             'lies in the near disk. DIRECTION MATTERS: g_q <= 0 on the q-side does NOT imply '
             'g_{q\'} <= 0 (e.g. r=1, A=(-3/5,0), C=(3/5,0), q=(0,4/5), q\'=(0,-4/5), p=q: g_q=-1 '
             'but g_{q\'}=39/25>0). The first version of this string had the containment reversed; '
             'lead retracted C894 for it. What IS used: (a) crescent cap inside B(q,r) is '
             'B(q,r) \\ int(B(q,r) cap B(q\',r)), so the crescent piece in H_q lies in B(q,r); '
             '(b) the overshoot of the single-disk constraint is exactly the half-lens '
             'B(q,r) cap B(q\',r) cap H_q, which lies in the distal disk B(q\',r); (c) hence on any '
             'region R with R cap B(q\',r) = empty, crescent <=> b in B(q,r) EXACTLY (both '
             'inclusions from the product sign g_q g_{q\'} <= 0).')
res['L3'] = ('parallelogram law: for b in B(q,r) cap B(q\',r),  |b-q|^2+|b-q\'|^2 <= 2r^2 and '
             '|q-m|^2+|q\'-m|^2 = 2|q-m|^2 = 2(r^2-|AC|^2/4)  =>  |b-m|^2 <= |AC|^2/4, so the loss '
             'region L is inside the Thales disk of the chord AC (compact localisation of the '
             'overshoot).')

# ======================================================================================
# [C] candidate readings
# ======================================================================================
import mpmath as mp
mp.mp.dps = 60
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(x[0]), 10**17), F(int(x[1]), 10**17)) for x in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
HUBA_RAW, HUBB_RAW = 0, 2
FAN_A = [4, 5, 6, 7, 8]       # hub 10 fan pins (faces [10,4,5]..[10,8,0])
FAN_B = [0, 1, 2, 3]          # hub 9 fan pins (faces [9,0,1]..[9,3,4])


def M(fr):
    return mp.mpf(fr.numerator) / mp.mpf(fr.denominator)


def Vec(fr):
    return mp.matrix([M(fr[0]), M(fr[1])])


ring = [Vec(Pf[i]) for i in NEW2RAW_RINGS]
hB, hA = Vec(Pf[HUBB_RAW]), Vec(Pf[HUBA_RAW])
r_f = mp.mpf('0.3799838531198388')
r_c249 = M(F(3799838531198387090485182, 10**25))
Cc = {'r_float(30d)': mp.nstr(r_f, 30), 'r_C249(30d)': mp.nstr(r_c249, 30)}


def nrm(u):
    return mp.sqrt(u[0]**2 + u[1]**2)


def rho(h1, h2, cc):
    cr = (h2[0] - h1[0]) * (cc[1] - h1[1]) - (h2[1] - h1[1]) * (cc[0] - h1[0])
    return mp.sqrt(nrm(h2 - h1)**2 * nrm(cc - h1)**2 * nrm(cc - h2)**2 / (4 * cr * cr))


def pin(i, rad):
    a_, b_ = ring[i], ring[(i + 1) % 9]
    m_ = (a_ + b_) / 2
    d_ = nrm(b_ - a_)
    n_ = mp.matrix([(b_[1] - a_[1]) / d_, -(b_[0] - a_[0]) / d_])
    k_ = mp.sqrt(rad * rad - d_ * d_ / 4)
    p1, p2 = m_ + k_ * n_, m_ - k_ * n_
    return (p1 if nrm(p1) < nrm(p2) else p2)


pins = {i: pin(i, r_f) for i in range(9)}
Cc['central_faces_rho_minus_r'] = {i: mp.nstr(rho(hA, hB, ring[i]) - r_c249, 4) for i in (0, 4)}
Cc['chain_pin_distances_minus_r'] = {
    'hubA': {i: mp.nstr(nrm(hA - pins[i]) - r_f, 6) for i in FAN_A},
    'hubB': {i: mp.nstr(nrm(hB - pins[i]) - r_f, 6) for i in FAN_B}}


def bary(ids, h):
    A_ = mp.matrix([[1, pins[i][0], pins[i][1]] for i in ids]).T
    lam = mp.lu_solve(A_, mp.matrix([1, h[0], h[1]]))
    return [lam[k] for k in range(3)]


lamA = bary([4, 6, 8], hA)
VA = sum(lamA[i] * lamA[j] * nrm(pins[[4, 6, 8][i]] - pins[[4, 6, 8][j]])**2
         for i in range(3) for j in range(3) if i < j)
Cc['hubA_weights_pins_4_6_8'] = [mp.nstr(x, 12) for x in lamA]
Cc['hubA_V_minus_r2'] = mp.nstr(VA - r_f**2, 6)
Cc['hubA_eps(barycentric)'] = mp.nstr(mp.sqrt(max(mp.mpf(0), r_f**2 - VA)), 6)
epsA = mp.sqrt(max(mp.mpf(0), r_f**2 - VA))
bA_A = (lamA[0] * pins[4] + lamA[1] * pins[6] + lamA[2] * pins[8])
Cc['b_A_coords'] = mp.nstr(bA_A.T, 12)

# best convex localisation of hub B over its chain pins (grid over faces of the simplex)
best = None
for ids in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 1, 2), (0, 1, 3), (0, 2, 3),
            (1, 2, 3), (0, 1, 2, 3)]:
    if len(ids) == 2:
        cand = [(t / 1000, [t / 1000, 1 - t / 1000]) for t in range(1001)]
    elif len(ids) == 3:
        cand = [((i / 60), [i / 60, j / 60, (60 - i - j) / 60])
                for i in range(61) for j in range(61 - i)]
    else:
        cand = [((i / 20), [i / 20, j / 20, kt / 20, (20 - i - j - kt) / 20])
                for i in range(21) for j in range(21 - i) for kt in range(21 - i - j)]
    for _, lam in cand:
        bb = mp.matrix([sum(lam[t] * pins[ids[t]][0] for t in range(len(ids))),
                        sum(lam[t] * pins[ids[t]][1] for t in range(len(ids)))])
        dd = nrm(hB - bb)
        if best is None or dd < best[0]:
            best = (dd, ids, lam, bb)
Cc['hubB_best_convex_localisation'] = {'eps': mp.nstr(best[0], 12), 'pins': list(best[1]),
                                       'weights': [mp.nstr(x, 8) for x in best[2]]}
# hub B pinned? = is hB inside conv(pins)?  (all barycentric signs of one triangle)
Cc['hubB_inside_conv_chain_pins'] = all(
    all(x >= -mp.mpf('1e-12') for x in bary(list(ids), hB))
    for ids in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)])


def disks_through(A_, C_, rad):
    m_ = (A_ + C_) / 2
    d_ = nrm(C_ - A_)
    n_ = mp.matrix([(C_[1] - A_[1]) / d_, -(C_[0] - A_[0]) / d_])
    k_ = mp.sqrt(rad * rad - d_ * d_ / 4)
    return m_ + k_ * n_, m_ - k_ * n_


faces = {}
for i in (0, 4):
    A_, C_ = hA, ring[i]
    qa, qb = disks_through(A_, C_, r_f)
    q = qa if abs(nrm(qa - hB) - r_f) < abs(nrm(qb - hB) - r_f) else qb
    qo = qb if q is qa else qa
    u = (C_ - A_) / nrm(C_ - A_)
    t = mp.matrix([-u[1], u[0]])
    if (q - A_)[0] * t[0] + (q - A_)[1] * t[1] < 0:
        t = -t
    faces[i] = dict(q=q, qo=qo, t=t, chord=nrm(C_ - A_) / 2, A=A_)
    Cc['face_%d' % i] = {
        '|AC|': mp.nstr(2 * faces[i]['chord'], 10),
        '|q-hB|-r (tightness of the fixed disk)': mp.nstr(nrm(q - hB) - r_f, 6),
        '|qo-hB|-r (distal clearance)': mp.nstr(nrm(qo - hB) - r_f, 6),
        'signed chord-line distance of hB': mp.nstr(abs((hB - A_)[0] * t[0] + (hB - A_)[1] * t[1]), 10),
        'Thales radius of chord': mp.nstr(faces[i]['chord'], 10)}


def proj_disk(y, cc, rad):
    v = y - cc
    n_ = nrm(v)
    return y if n_ <= rad else cc + (rad / n_) * v


def proj_intersection(y, disks, it=400):
    x = y
    for _ in range(it):
        for (cc, rad) in disks:
            x = proj_disk(x, cc, rad)
    return x


KA = [(mp.matrix([0, 0]), 1 - r_f)] + [(pins[i], r_f) for i in FAN_A]
KB = [(mp.matrix([0, 0]), 1 - r_f)] + [(pins[i], r_f) for i in FAN_B]
Cc['max_violation_K_A(hA)'] = mp.nstr(max(nrm(hA - cc) - rad for cc, rad in KA), 6)
Cc['max_violation_K_B(hB)'] = mp.nstr(max(nrm(hB - cc) - rad for cc, rad in KB), 6)

# --- the exact reduction margin -----------------------------------------------------
# b_B = (p_0+p_3)/2 exactly (rational weights 1/2,1/2 on two *chain* pins of hub B);
# localisation: every feasible hub B lies in B(b_B, eps_B)   [variance identity]
bB = (pins[0] + pins[3]) / 2
eps_B = mp.sqrt(max(mp.mpf(0), r_f**2 - (nrm(pins[0] - pins[3]) / 2)**2))
Cc['b_B_coords_((p0+p3)/2)'] = mp.nstr(bB.T, 12)
Cc['eps_B_ring_only'] = mp.nstr(eps_B, 12)
Cc['|hB-b_B|'] = mp.nstr(nrm(hB - bB), 12)
Cc['|hB-p0|-r, |hB-p3|-r'] = [mp.nstr(nrm(hB - pins[i]) - r_f, 6) for i in (0, 3)]

for i, f in faces.items():
    q, qo = f['q'], f['qo']
    # closest point of B(qo,r) to hB; it is feasible for the other two constraints at the
    # candidate (checked), so dist(hB, L_i) = |hB-qo| - r
    yproj = proj_disk(hB, qo, r_f)
    feasible = (nrm(yproj - q) <= r_f) and (((yproj - f['A'])[0] * f['t'][0]
                                            + (yproj - f['A'])[1] * f['t'][1]) >= 0)
    Cc['face_%d' % i].update({
        'projection_of_hB_on_distal_disk_is_feasible_for_the_rest':
            'yes' if feasible else 'no',
        'dist(hB, loss region L)': mp.nstr(nrm(hB - qo) - r_f, 10),
        'dist(b_B, distal disk) - eps_B  (exactness margin)':
            mp.nstr(nrm(bB - qo) - r_f - eps_B, 10),
        'B(b_B,eps_B) misses the distal disk?':
            'yes' if nrm(bB - qo) - r_f > eps_B else 'NO'})
    # disk centres evaluated at h_A vs a perturbed A of size eps_A (pinning sensitivity)
    qsens = mp.mpf(0)
    for ang in (0, mp.pi / 2, mp.pi, 3 * mp.pi / 2):
        Ap = hA + epsA * mp.matrix([mp.cos(ang), mp.sin(ang)])
        qp = disks_through(Ap, ring[i], r_f)
        qp = [x for x in qp if abs(nrm(x - hB) - r_f) < mp.mpf('1e-3')][0]
        qsens = max(qsens, nrm(qp - q))
    Cc['face_%d' % i]['disk-centre shift for |dA|=eps_A'] = mp.nstr(qsens, 6)

res['C_candidate'] = Cc
(OUT / 'central_crescent_stress.json').write_text(json.dumps(res, indent=2), encoding='utf-8')
for key, val in res.items():
    if key.startswith('S'):
        print('==', key, '=', val)
    if key.startswith('L'):
        print('==', key, ':', val[:150], '...')
print(json.dumps(Cc, indent=2))
