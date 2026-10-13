"""r20-rigidity: independent audit of the uniform-simplex certificate (C911 forces reused read-only).

No lead helper code: the 51-edge graph is rebuilt from the written description, the anchor loads are
recomputed by exact Fraction incidence summation of the STORED rational forces, and the radial-work /
vertex-work checks use my own interval minimum expression. Tasks:

  (1) graph + exact free-node divergence (re-verification);
  (2) 9-vertex work: y^j = (1-t)/9 * ones + t e_j, Delta_i = L - D y_i, theta_i = sum_{k<i} Delta_k,
      f(v^j) = sum_i l_i . U(theta_i); verify sum Delta = 2 pi exactly and the vertex minimum;
  (3) whole simplex: y_i >= 31/450, sum y = 1.  For each i the exact attainable range of the partial
      sum S_i = sum_{k<i} y_k is [(i-1)*31/450, 1-(9-i)*31/450], hence
      theta_i in [i L - D (1-(9-i)*31/450), i L - D (i-1)*31/450] (theta decreasing in S_i).
      Check l_i . U(theta) >= 0 on that whole interval (kappa_i = 0 certificate, no Taylor penalty);
  (4) equivalence of the width cap Delta_max = L - 31D/450 with y_i >= 31/450 (exact identity);
  (5) the WORK l_i.U(theta_i) is theta dependent (tracked by kappa_i); no constant-phase
      assumption is made and no phase-spread claim is used.

Exact rationals where rational; only cos/sin/sqrt/pi are interval. Asserts are hard. Writes
audit_uniform_simplex.json/.log.
"""
import json
from pathlib import Path
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 80
mp.iv.dps = 65
R20 = Path(__file__).resolve().parent
LEAD = R20.parent / 'lead'
cert = json.loads((LEAD / 'uniform_sector_certificate.json').read_text(encoding='utf-8'))
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


def I(x):
    x = F(x)
    return mp.iv.mpf(x.numerator) / x.denominator


def MIN_G(a, b, tlo, thi, PI_LO):
    """Exact minimum of g(t) = a cos t + b sin t over t in [tlo, thi] (intervals).

    g(t) = R cos(t - phi), R = sqrt(a^2+b^2), phi = atan2(b, a); cos decreases in |t - phi| on [0, pi].
    If a > 0 then |phi| < pi/2, and if the whole interval lies in (-pi/2, pi/2) then every
    |t - phi| <= pi, so the minimum over the interval is attained at an ENDPOINT.  Otherwise the
    interior minimum -R cannot be excluded and is included conservatively."""
    R = mp.iv.sqrt(a * a + b * b)
    ga = a * mp.iv.cos(tlo) + b * mp.iv.sin(tlo)
    gb = a * mp.iv.cos(thi) + b * mp.iv.sin(thi)
    cand = [mp.mpf(ga.a), mp.mpf(gb.a)]
    excl = bool(mp.mpf(a.a) > 0 and mp.mpf(tlo.a) > -PI_LO / 2 and mp.mpf(thi.b) < PI_LO / 2)
    if not excl:
        cand.append(-mp.mpf(R.b))
    return min(cand), excl


# ---------------------------------------------------------------- (1) graph + divergence
faces = [[9, k, k + 1] for k in range(4)] + [[10, k, (k + 1) % 9] for k in range(4, 9)] \
        + [[9, 10, 0], [9, 10, 4]]
edges = []
for s in range(9):
    edges.extend([(9 + s, s), (9 + s, (s - 1) % 9)])
for j, face in enumerate(faces):
    edges.extend((9 + s, 20 + j) for s in face)
assert edges == [tuple(e) for e in cert['edges']], 'graph mismatch'
p = [[F(v) for v in row] for row in cert['forces_rational']]
bal = [[F(0), F(0)] for _ in range(31)]
for (v, w), q in zip(edges, p):
    for k in range(2):
        bal[v][k] += q[k]
        bal[w][k] -= q[k]
free_ok = all(x == 0 for row in bal[9:] for x in row)
assert free_ok, 'free-node divergence not exactly zero'
l = [bal[i] for i in range(9)]
say('[S1] graph identical to stored edges ; free-node divergence exactly zero (Fraction) ;')
say('     anchor loads l_i = (%s, %s) for i=0..8' % ('a_i', 'd_i'))

# ---------------------------------------------------------------- anchors in the radial frame
n_i, t_i, a_i, d_i, R_i, phi_i = [], [], [], [], [], []
for i in range(9):
    th = 2 * mp.iv.pi * i / 9
    n_i.append((mp.iv.cos(th), mp.iv.sin(th)))
    t_i.append((-mp.iv.sin(th), mp.iv.cos(th)))
    a_ = I(l[i][0]) * n_i[i][0] + I(l[i][1]) * n_i[i][1]
    d_ = I(l[i][0]) * t_i[i][0] + I(l[i][1]) * t_i[i][1]
    a_i.append(a_)
    d_i.append(d_)
    R_i.append(mp.iv.sqrt(a_ * a_ + d_ * d_))
    phi_i.append(mp.iv.atan2(d_, a_))
say('[S2] radial frame per anchor: l_i . U(theta_i) = a_i cos t + d_i sin t with t = theta_i - 2 pi i / 9 ;\n')
say('     the WORK l_i.U(theta_i) is theta dependent (this is what kappa_i tracks); no constant-phase assumption is made.')

# ---------------------------------------------------------------- (3) whole-simplex radial work
Lc = F(19, 50)
L = 2 * mp.iv.atan2(I(Lc), mp.iv.sqrt(1 - I(Lc) ** 2))       # L = 2 asin(19/50), via atan2
# L is DEFINED by L = 2 atan2(19/50, sqrt(1-(19/50)^2)) (the atan formula is the identity);
# the sin enclosure below is only a consistency diagnostic, not a proof of the identity
_c = mp.iv.sin(L / 2)
assert mp.mpf(_c.a) <= mp.mpf(I(Lc).a) and mp.mpf(I(Lc).b) <= mp.mpf(_c.b), \
    'L does not satisfy sin(L/2) = 19/50'
D = 9 * L - 2 * mp.iv.pi
assert D > 0, 'deficit must be positive'
PI_LO_ = mp.mpf(mp.iv.pi.a)
ymin = F(31, 450)
say('[S3] L = 2 asin(19/50) ; D = 9L - 2pi > 0 ; scope y_i >= 31/450 and sum y = 1')
radial = []
for i in range(1, 9):                        # theta_0 = 0 is fixed, so i=0 contributes a_0 only
    lo_S, hi_S = i * ymin, F(1) - (9 - i) * ymin   # S_i = sum_{j<i} y_j has i terms
    lo_th = i * L - D * I(hi_S)              # theta decreases in S_i
    hi_th = i * L - D * I(lo_S)
    m_, excl = MIN_G(a_i[i], d_i[i], lo_th - i * 2 * mp.iv.pi / 9, hi_th - i * 2 * mp.iv.pi / 9, PI_LO_)
    # NOTE: the radial frame is OFFSET: l_i . U(theta_i) = a_i cos t + d_i sin t with
    # t = theta_i - 2 pi i / 9 (the anchor base angle).  Evaluating in the absolute frame is WRONG.
    ok = m_ >= 0
    radial.append({'i': i, 'S_range': [str(lo_S), str(hi_S)],
                   'theta_lo': mp.nstr(mp.mpf(lo_th.a), 18), 'theta_hi': mp.nstr(mp.mpf(hi_th.b), 18),
                   'min_work': mp.nstr(m_, 18), 'nonneg': bool(ok), 'interior_min_excluded': bool(excl)})
    say('     i=%d  S_i in [%s, %s] -> theta in [%s, %s] ; min l_i.U = %s >= 0 : %s'
        % (i, lo_S, hi_S, mp.nstr(mp.mpf(lo_th.a), 14), mp.nstr(mp.mpf(hi_th.b), 14),
           mp.nstr(m_, 14), bool(ok)))
say('     i=0: theta_0 = 0 fixed -> l_0.U = a_0 = %s' % mp.nstr(mp.mpf(a_i[0].a), 18))
say('     a_0 >= 0 : %s ; ALL interior radial works >= 0 on the WHOLE simplex : %s'
    % (bool(mp.mpf(a_i[0].a) >= 0), all(r['nonneg'] for r in radial)))
assert all(r['nonneg'] for r in radial), 'radial work negative on the whole simplex'

# ---------------------------------------------------------------- (5) the 9-vertex cell at t = 19/50
tbest = F(19, 50)
ys = [[F(1 - tbest, 9) + (tbest if i == j else 0) for i in range(9)] for j in range(9)]
thetas = []
for y in ys:
    th = [mp.iv.mpf(0)]
    for i in range(8):
        th.append(th[-1] + L - D * I(y[i]))
    thetas.append(th)
rng = []
for i in range(9):
    rng.append((min(mp.mpf(th[i].a) for th in thetas), max(mp.mpf(th[i].b) for th in thetas)))
say('[S6] cell = conv of the 9 vertices at t = 19/50 ; coordinate ranges and kappa:')
kappa_cell = []
for i in range(9):
    a_, z_ = rng[i]
    m_, excl = MIN_G(a_i[i], d_i[i], mp.iv.mpf(a_) - i * 2 * mp.iv.pi / 9,
                     mp.iv.mpf(z_) - i * 2 * mp.iv.pi / 9, PI_LO_)
    kappa_cell.append(max(mp.mpf(0), -m_))
    say('     i=%d theta in [%.6f, %.6f] (width %.6f) ; min l_i.U = %.10f ; kappa_i = %s'
        % (i, a_, z_, z_ - a_, m_, mp.nstr(kappa_cell[i], 8)))
say('     kappa = 0 for every anchor on the CELL : %s' % all(k == 0 for k in kappa_cell))
assert all(k == 0 for k in kappa_cell), 'kappa not zero at t = 19/50'
assert tbest == F(19, 50), 'this cell must be the t = 19/50 cell'
works = []
for th in thetas:
    works.append(sum(I(l[i][0]) * mp.iv.cos(th[i]) + I(l[i][1]) * mp.iv.sin(th[i]) for i in range(9)))
vmin = min(mp.mpf(w.a) for w in works)
cellvmin = vmin          # dedicated: this is the t = 19/50 value
assert cellvmin > mp.mpf(19) / 50, 'cell vertex minimum not above 19/50 at t = 19/50'
say('     vertex minimum over the 9 vertices = %s ; > 19/50 : %s'
    % (mp.nstr(vmin, 20), bool(vmin > mp.mpf(19) / 50)))

# ---------------------------------------------------------------- (4) width-cap equivalence
dmax = L - D * I(ymin)
say('     Delta_max = L - D*(31/450) = [' + mp.nstr(mp.mpf(dmax.a), 18) + ', '
    + mp.nstr(mp.mpf(dmax.b), 18) + ']')
say('     Delta_i <= Delta_max <-> y_i >= 31/450 holds identically since Delta_i = L - D y_i with '
    'D > 0 ; y_min fraction check = ' + str(F(31, 450) == ymin))
assert D > 0
# the two endpoint identities of the simplex in angle space
say('     checks: Delta_i(1) = L - D = 2pi - 8L = %s ; Delta_i(0) = L = %s'
    % (mp.nstr(mp.mpf((L - D).b), 18), mp.nstr(mp.mpf(L.b), 18)))

# ---------------------------------------------------------------- (2) the 9 vertices
best = {}
for n in range(1, 101):
    t = F(n, 100)
    ys = [[F(1 - t, 9) + (t if i == j else 0) for i in range(9)] for j in range(9)]
    assert all(sum(y) == 1 for y in ys)
    works = []
    for y in ys:
        th = [mp.iv.mpf(0)]
        for i in range(8):
            th.append(th[-1] + L - D * I(y[i]))
        assert abs(mp.mpf((th[8] + L - D * I(y[8])).b) - mp.mpf(2 * mp.iv.pi.a)) < mp.mpf('1e-40'), \
            'vertex angle vectors must sum to 2 pi'
        works.append(sum(I(l[i][0]) * mp.iv.cos(th[i]) + I(l[i][1]) * mp.iv.sin(th[i])
                         for i in range(9)))
    vmin = min(mp.mpf(w.a) for w in works)
    best[t] = vmin
passed = [t for t, v in best.items() if v > mp.mpf(19) / 50]
say('[S5] 9-vertex work: %d of 100 tested rational t give vertex minimum > 19/50 ; max t = %s'
    % (len(passed), max(passed) if passed else None))
if passed:
    tmax = max(passed)
    say('     at t = %s : vertex minimum lower bound = %s > 19/50 : %s'
        % (tmax, mp.nstr(best[tmax], 20), bool(best[tmax] > mp.mpf(19) / 50)))
    assert best[tmax] > mp.mpf(19) / 50

OUT = {'graph_identical': True, 'free_divergence_zero': True, 'work_theta_dependent': True,
       'cell_kappa_all_zero': all(k == 0 for k in kappa_cell),
       'cell_vertex_min_at_19_50': mp.nstr(cellvmin, 20),
       'whole_simplex_kappa_zero': all(r['nonneg'] for r in radial),
       'whole_simplex_radial': radial, 'kappa_all_zero_on_simplex': all(r['nonneg'] for r in radial),
       'a0_nonneg': bool(mp.mpf(a_i[0].a) >= 0),
       'width_cap_equiv': True, 'best_t': (str(max(passed)) if passed else None),
       'best_vertex_min': (mp.nstr(best[max(passed)], 20) if passed else None),
       'status': 'independent audit; the printed identities/endpoints are the evidence, not PASS flags',
       'repro': 'py -3 -B -X utf8 audit_uniform_simplex.py'}
(R20 / 'audit_uniform_simplex.json').write_text(json.dumps(OUT, indent=2))
(R20 / 'audit_uniform_simplex.log').write_text('\n'.join(REP) + '\n')
say('\nwritten audit_uniform_simplex.json / .log')
