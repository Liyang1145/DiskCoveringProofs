"""r20-rigidity (step 11): the LOCAL RIGIDITY structure at the registered ideal object X60.

Object:  X60 = research-2026/session2/n11alg/cert_sym60.json  (22 integers / 1e60),
         the mirror-symmetric object whose radius is the registered R_stru
         (RD_interval lo = 0.3799838531198386897222616061360932143087189561...).

Decidable questions (all at 120 dps, exact rational input):
  B1  active set (18 of 20 critical points), exact equality of the 18 values
  B2  mirror structure: axis, site pairing, invariance of the active set
  B3  J18 at X60: singular values, kernel dim, kernel decomposition Sym/Anti
  B4  RIGIDITY:  rank(J18 | Sym) and rank(J18 | Anti)
        rank(J18|Sym) = 10  => the pinned system is locally RIGID (unique up to
                               rotation) inside the mirror-symmetric locus
        dim(ker J18 cap Anti) = 4 => 4 first-order flat SYMMETRY-BREAKING directions
  B5  Danskin stationarity: is there u > 0 on the simplex with ||J^T u|| = 0 ?
  B6  MIXED TANGENT CONES (all of them, not a sample): the second-order min-max
        c_k = min_{||v||=1, v in ker(J18)/rotation} max_i v^T H_i v
      via the concave dual  c_k = max_{lambda in simplex} lambda_min(Q^T (sum_i
      lambda_i H_i) Q),  Q = orthonormal basis of ker(J18) cap Anti.
      The certificate is an explicit rational lambda + an interval LDL positivity
      check of  Q^T M_lambda Q - c0 I  (positive definite => c_k > 0 for ALL
      directions, all faces of the tangent cone, not a sampled subset).
  B7  the transverse linear rate mu = min_{||v||=1, v perp ker J18} max_i grad f_i . v

No registered claim; numeric + interval diagnosis with explicit repro.
"""
import json, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
DPS = 120
mp.mp.dps = DPS
N = 11
IVDPS = 60

raw60 = json.loads((ROOT / 'research-2026/session2/n11alg/cert_sym60.json').read_text(encoding='utf-8-sig'))
X = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 60 for v in a]) for a in raw60['centers_scaled_1e60']]
RD_LO = mp.mpf(raw60['RD_interval'][0].split(',')[0].lstrip('['))


def circ(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def bis_bd(C, i, j, sgn):
    dv = C[i] - C[j]
    d2 = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / d2 * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(d2), dv[0] / mp.sqrt(d2)])
    s2 = 1 - sum(A0[t] ** 2 for t in range(2))
    return None if s2 <= 0 else mp.matrix([A0[t] + sgn * mp.sqrt(s2) * nv[t] for t in range(2)])


def dd(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def critical_set(C):
    crit = []
    for tri in itertools.combinations(range(N), 3):
        u = circ(C, tri)
        if u is None or sum(u[t] ** 2 for t in range(2)) > 1:
            continue
        ds = sorted((dd(u, C[q]), q) for q in range(N))
        if set(q for _, q in ds[:3]) == set(tri):
            crit.append((ds[0][0], 'V3', tuple(tri), None,
                         (lambda CC, s=tri: dd(circ(CC, s), CC[s[0]]))))
    for i, j in itertools.combinations(range(N), 2):
        for sgn in (1, -1):
            p = bis_bd(C, i, j, sgn)
            if p is None:
                continue
            ds = sorted((dd(p, C[q]), q) for q in range(N))
            if set(q for _, q in ds[:2]) == {i, j}:
                crit.append((ds[0][0], 'V2b', (i, j), sgn,
                             (lambda CC, a=i, b=j, g=sgn: dd(bis_bd(CC, a, b, g), CC[a]))))
    return crit


crit = critical_set(X)
g0 = max(v for v, *_ in crit)
tight = [c for c in crit if c[0] > g0 - mp.mpf('1e-9')]
print('B1  #critical = %d  #tight = %d  gamma(X60) = %s' % (len(crit), len(tight), mp.nstr(g0, 45)))
print('    registered RD_interval lo = %s   (gamma - lo = %s)'
      % (mp.nstr(RD_LO, 45), mp.nstr(g0 - RD_LO, 6)))
print('    spread of the 18 tight values = %s' % mp.nstr(max(v for v, *_ in tight) - min(v for v, *_ in tight), 6))
print('    slack levels (non-tight critical): %s'
      % [mp.nstr(v - g0, 8) for v, *_ in sorted(crit, key=lambda t: -t[0]) if v < g0 - mp.mpf('1e-9')])
sites_tight = [(k, s) for v, k, s, sg, f in tight]
print('    tight list:', sites_tight)

# ------------------------------------------------------------------ B2 mirror
mp.mp.dps = DPS
ang = [mp.atan2(X[i][1], X[i][0]) for i in range(N)]
mod = [mp.sqrt(X[i][0] ** 2 + X[i][1] ** 2) for i in range(N)]


def refl(p, a):
    c, s = mp.cos(2 * a), mp.sin(2 * a)
    return mp.matrix([c * p[0] + s * p[1], s * p[0] - c * p[1]])


cand_axes = []
for i in range(N):
    for j in range(i + 1, N):
        if abs(mod[i] - mod[j]) < mp.mpf('1e-40'):
            cand_axes.append(((ang[i] + ang[j]) / 2, (i, j)))
best_axis, best_pair, best_mm = None, None, mp.inf
for a0, pr in cand_axes:
    for off in (mp.mpf(0), mp.pi / 2):
        aa = a0 + off
        mm = max(min(dd(refl(X[i], aa), X[j]) for j in range(N)) for i in range(N))
        if mm < best_mm:
            best_axis, best_pair, best_mm = aa, pr, mm
print('\nB2  mirror axis = %s deg (from pair %s)  mismatch = %s'
      % (mp.nstr(best_axis * 180 / mp.pi, 25), best_pair, mp.nstr(best_mm, 6)))
pairing = [int(min(range(N), key=lambda j: dd(refl(X[i], best_axis), X[j]))) for i in range(N)]
print('    pairing i -> sigma(i):', pairing)
inv = all(pairing[pairing[i]] == i for i in range(N))
print('    involution:', inv, ' fixed sites:', [i for i in range(N) if pairing[i] == i])
print('    active-set invariance under the pairing:',
      sorted([sorted(pairing[q] for q in s) for k, s in sites_tight]) ==
      sorted([sorted(s) for k, s in sites_tight]))

# projectors Sym / Anti
R = mp.matrix([[mp.cos(2 * best_axis), mp.sin(2 * best_axis)],
               [mp.sin(2 * best_axis), -mp.cos(2 * best_axis)]])


def split(v):
    vs = mp.matrix(22, 1)
    va = mp.matrix(22, 1)
    done = set()
    for i in range(N):
        if i in done:
            continue
        j = pairing[i]
        if j == i:
            u = mp.matrix([X[i][0], X[i][1]])
            un = u / mp.sqrt(u[0] ** 2 + u[1] ** 2)
            comp = v[2 * i] * un[0] + v[2 * i + 1] * un[1]
            for t in range(2):
                vs[2 * i + t] = comp * un[t]
                va[2 * i + t] = v[2 * i + t] - comp * un[t]
            done.add(i)
        else:
            vi = mp.matrix([v[2 * i], v[2 * i + 1]])
            vj = mp.matrix([v[2 * j], v[2 * j + 1]])
            si = (vi + R * vj) / 2
            sj = (vj + R * vi) / 2
            ai = vi - si
            aj = vj - sj
            for t in range(2):
                vs[2 * i + t], vs[2 * j + t] = si[t], sj[t]
                va[2 * i + t], va[2 * j + t] = ai[t], aj[t]
            done.update((i, j))
    return vs, va


# ------------------------------------------------------------------ B3 J18
def fval(f, C):
    return f(C)


HJ = mp.mpf('1e-25')


def grad(f, C):
    g = []
    for i in range(N):
        for t in range(2):
            Cp = [mp.matrix(C[k]) for k in range(N)]
            Cm = [mp.matrix(C[k]) for k in range(N)]
            Cp[i][t] += HJ
            Cm[i][t] -= HJ
            g.append((f(Cp) - f(Cm)) / (2 * HJ))
    return g


J = mp.matrix([grad(f, X) for v, k, s, sg, f in tight])
print('\nB3  J18 built (18x22), listed singular values:')
G = J * J.T
ev = sorted(mp.eigsy(G, eigvals_only=True), reverse=True)
sig = [mp.sqrt(max(e, mp.mpf(0))) for e in ev]
print('    ' + ' '.join(mp.nstr(s, 10) for s in sig))
print('    sigma_min = %s   sigma_2nd = %s' % (mp.nstr(sig[-1], 6), mp.nstr(sig[-2], 12)))

# kernel of J  (eigenvectors of J^T J with the 18 small eigenvalues)
Gt = J.T * J
evt, Vt = mp.eigsy(Gt)
order = sorted(range(22), key=lambda k: evt[k])
ker = [Vt[:, k] for k in order if abs(evt[k]) < mp.mpf('1e-40')]
print('    dim ker(J18) = %d   (|J k|_inf for the kernel basis: %s)'
      % (len(ker), [mp.nstr(max(abs(sum(J[i, j] * kk[j] for j in range(22))) for i in range(18)), 4)
                    for kk in ker]))
rotv = mp.matrix([x for i in range(N) for x in (-X[i][1], X[i][0])])
rotv = rotv / mp.sqrt(sum(x ** 2 for x in rotv))
# dimension of ker cap Sym / ker cap Anti
Sym_k, Anti_k = [], []
for kk in ker:
    vs, va = split(kk)
    if mp.sqrt(sum(x ** 2 for x in vs)) > mp.mpf('1e-20'):
        Sym_k.append((kk, mp.sqrt(sum(x ** 2 for x in vs))))
    if mp.sqrt(sum(x ** 2 for x in va)) > mp.mpf('1e-20'):
        Anti_k.append((kk, mp.sqrt(sum(x ** 2 for x in va))))
print('    kernel basis symmetry profile (|Sym part|, |Anti part|):')
for kk in ker:
    vs, va = split(kk)
    print('      |Sym| = %s   |Anti| = %s   |cos with rotation| = %s'
          % (mp.nstr(mp.sqrt(sum(x ** 2 for x in vs)), 5),
             mp.nstr(mp.sqrt(sum(x ** 2 for x in va)), 5),
             mp.nstr(abs(sum(kk[t] * rotv[t] for t in range(22))), 5)))

# ------------------------------------------------------------------ B4 ranks
def rank_on(proj_list):
    """rank of J restricted to span(proj_list)"""
    B = mp.matrix(22, len(proj_list))
    for j, v in enumerate(proj_list):
        for i in range(22):
            B[i, j] = v[i]
    # orthonormalise
    Q, _ = mp.qr_solve(B, mp.matrix(22, 1))[:2] if False else (None, None)
    # Gram-Schmidt at high precision
    cols = []
    for j in range(len(proj_list)):
        w = mp.matrix([B[i, j] for i in range(22)])
        for c in cols:
            w = w - (sum(c[i] * w[i] for i in range(22))) * c
        nw = mp.sqrt(sum(w[i] ** 2 for i in range(22)))
        if nw > mp.mpf('1e-25'):
            cols.append(w / nw)
    Qb = mp.matrix(22, len(cols))
    for j, c in enumerate(cols):
        for i in range(22):
            Qb[i, j] = c[i]
    M = J * Qb
    GM = M.T * M
    evm = mp.eigsy(GM, eigvals_only=True)
    s = [mp.sqrt(max(e, mp.mpf(0))) for e in sorted(evm, reverse=True)]
    rk = sum(1 for x in s if x > mp.mpf('1e-3'))
    return rk, [mp.nstr(x, 8) for x in s], len(cols)


# basis of Sym and Anti
e = [mp.matrix(22, 1) for _ in range(22)]
for i in range(22):
    e[i][i] = 1
SymB, AntiB = [], []
for i in range(22):
    vs, va = split(e[i])
    if mp.sqrt(sum(x ** 2 for x in vs)) > mp.mpf('1e-25'):
        SymB.append(vs)
    if mp.sqrt(sum(x ** 2 for x in va)) > mp.mpf('1e-25'):
        AntiB.append(va)
# deduplicate (the projectors of e_i repeat)
def gs(vecs, tol=mp.mpf('1e-25')):
    out = []
    for v in vecs:
        w = mp.matrix([v[i] for i in range(22)])
        for c in out:
            w = w - sum(c[i] * w[i] for i in range(22)) * c
        nw = mp.sqrt(sum(w[i] ** 2 for i in range(22)))
        if nw > tol:
            out.append(w / nw)
    return out


SymB, AntiB = gs(SymB), gs(AntiB)
print('\nB4  dim Sym = %d   dim Anti = %d' % (len(SymB), len(AntiB)))
rkS, sS, dS = rank_on(SymB)
rkA, sA, dA = rank_on(AntiB)
print('    rank(J | Sym) = %d / %d ; singular values %s' % (rkS, dS, sS))
print('    rank(J | Anti) = %d / %d ; singular values %s' % (rkA, dA, sA))

# ------------------------------------------------------------------ B5 Danskin
u = mp.matrix(18, 1)
# left null vector: eigenvector of J J^T for the zero eigenvalue, normalised to sum 1
evG, VG = mp.eigsy(G)
kmin = min(range(18), key=lambda k: evG[k])
for i in range(18):
    u[i] = VG[i, kmin]
s = sum(u[i] for i in range(18))
u = u / s
res = mp.matrix([sum(u[i] * J[i, j] for i in range(18)) for j in range(22)])
print('\nB5  Danskin: u (eigenvector for lambda_min(JJ^T)) sum-normalised:')
print('    min u_i = %s   max u_i = %s   all > 0: %s'
      % (mp.nstr(min(u[i] for i in range(18)), 6), mp.nstr(max(u[i] for i in range(18)), 6),
         bool(all(u[i] > 0 for i in range(18)))))
print('    || J^T u ||_inf = %s   (Frobenius scale ||J|| = %s)'
      % (mp.nstr(max(abs(x) for x in res), 6), mp.nstr(sig[0], 8)))

json.dump({'gamma': mp.nstr(g0, 45), 'RD_lo': mp.nstr(RD_LO, 45),
           'n_critical': len(crit), 'n_tight': len(tight),
           'tight': [[k, list(s)] for k, s in sites_tight],
           'mirror_axis_deg': mp.nstr(best_axis * 180 / mp.pi, 25), 'pairing': pairing,
           'sigma': [mp.nstr(x, 12) for x in sig],
           'ker_dim': len(ker), 'rank_Sym': rkS, 'rank_Anti': rkA,
           'u_min': mp.nstr(min(u[i] for i in range(18)), 8),
           'uJ_inf': mp.nstr(max(abs(x) for x in res), 8)},
          open(P / 'r20_mixed_tangent_part1.json', 'w'), indent=2)

# ------------------------------------------------------------------ B6 SDP
print('\nB6  second-order min-max over ker(J18) cap Anti (mixed tangent cones)')
# orthonormal basis of ker cap Anti
AntiK = []
for kk in ker:
    vs, va = split(kk)
    n = mp.sqrt(sum(x ** 2 for x in va))
    if n > mp.mpf('1e-20'):
        AntiK.append(va / n)
AntiK = gs(AntiK)
print('    dim (ker cap Anti) = %d' % len(AntiK))
# orthonormalise against the rotation direction as well (rotation is in Sym, so
# ker cap Anti is automatically orthogonal to it only approximately; project out)
rotproj = []
for v in AntiK:
    w = v - sum(rotv[i] * v[i] for i in range(22)) * rotv
    rotproj.append(w)
AntiK = gs(rotproj)
print('    after removing the rotation component: dim = %d' % len(AntiK))

HD = mp.mpf('1e-16')


def hess(f, C):
    H = mp.zeros(22, 22)
    for a in range(22):
        for b in range(a, 22):
            def at(sa, sb):
                Cv = [mp.matrix(C[k]) for k in range(N)]
                Cv[a // 2][a % 2] += sa * HD
                Cv[b // 2][b % 2] += sb * HD
                return f(Cv)
            v = (at(1, 1) - at(1, -1) - at(-1, 1) + at(-1, -1)) / (4 * HD ** 2)
            H[a, b] = v
            H[b, a] = v
    return H


Hs = [hess(f, X) for v, k, s, sg, f in tight]
print('    Hessians built (18 x 22 x 22) at dps=%d, h=%s' % (DPS, HD))
# float64 copies for the optimiser
Hf = np.array([[[float(Hs[i][a, b]) for b in range(22)] for a in range(22)] for i in range(18)])
Qf = np.array([[float(AntiK[j][i]) for j in range(len(AntiK))] for i in range(22)])   # 22 x 4
print('    ||Q^T J^T||_inf = %.3e   (Q must lie in ker J)' % np.abs(Qf.T @ np.array([[float(J[i, j]) for j in range(22)] for i in range(18)]).T).max())


def lam_min(lam):
    M = np.einsum('i,iab->ab', lam, Hf)
    A = Qf.T @ M @ Qf
    A = (A + A.T) / 2
    w = np.linalg.eigvalsh(A)
    return w[0]


from scipy.optimize import minimize as spmin
best = None
for t in range(12):
    lam0 = np.random.default_rng(t).dirichlet(np.ones(18))
    o = spmin(lambda l: -lam_min(l), lam0, method='SLSQP',
              constraints=[{'type': 'eq', 'fun': lambda l: l.sum() - 1}], bounds=[(0, 1)] * 18,
              options={'maxiter': 3000, 'ftol': 1e-18})
    if best is None or o.fun < best.fun:
        best = o
lam = best.x
c_num = -best.fun
print('    float64 SDP: max_lambda lambda_min = %.10f   (argmax lambda min %.4f, #active>1e-6: %d)'
      % (c_num, lam.min(), int((lam > 1e-6).sum())))
act = [i for i in range(18) if lam[i] > 1e-6]
print('    active constraint indices at the optimum:', act,
      [(tight[i][1], list(tight[i][2])) for i in act])
# high-precision refinement of lambda on the simplex (projected subgradient ascent)
lam_mp = mp.matrix([mp.mpf(float(x)) for x in lam])


def lam_min_mp(lamv, return_vec=False):
    M = mp.zeros(22, 22)
    for i in range(18):
        for a in range(22):
            for b in range(22):
                M[a, b] += lamv[i] * Hs[i][a, b]
    A = mp.zeros(len(AntiK), len(AntiK))
    for p in range(len(AntiK)):
        for q in range(len(AntiK)):
            A[p, q] = sum(AntiK[p][a] * M[a, b] * AntiK[q][b] for a in range(22) for b in range(22))
    A = (A + A.T) / 2
    ev, V = mp.eigsy(A.replace(mp.matrix(A)))
    k = min(range(len(AntiK)), key=lambda t: ev[t])
    val = ev[k]
    vec = mp.matrix([V[i, k] for i in range(len(AntiK))])
    return (val, vec) if return_vec else val


step = mp.mpf('0.05')
cur = lam_mp
curval = lam_min_mp(cur)
bestmp = (curval, cur)
for it in range(400):
    val, vec = lam_min_mp(cur, True)
    z = mp.matrix(22, 1)
    for a in range(22):
        z[a] = sum(AntiK[p][a] * vec[p] for p in range(len(AntiK)))
    g = [sum(z[a] * Hs[i][a, b] * z[b] for a in range(22) for b in range(22)) for i in range(18)]
    nxt = mp.matrix([cur[i] + step * g[i] for i in range(18)])
    nxt = mp.matrix([max(x, mp.mpf(0)) for x in nxt])
    nxt = nxt / sum(nxt[i] for i in range(18))
    v2 = lam_min_mp(nxt)
    if v2 > val:
        cur, curval = nxt, v2
        if v2 > bestmp[0]:
            bestmp = (v2, nxt)
    else:
        step = step * mp.mpf('0.7')
    if it % 100 == 99:
        step = step * 2
print('    high-precision refinement: lambda_min = %s (certificate candidate)' % mp.nstr(bestmp[0], 20))

# rigorous-enough interval check: A(lambda) - c0 I positive definite via interval LDL
lamc = bestmp[1]
c0 = bestmp[0] - mp.mpf('1e-8')
mp.mp.dps = IVDPS
mp.iv.dps = IVDPS
ivX = [mp.matrix([mp.iv.mpf(int(v)) / mp.iv.mpf(10) ** 60 for v in a]) for a in
       json.loads((ROOT / 'research-2026/session2/n11alg/cert_sym60.json').read_text(encoding='utf-8-sig'))['centers_scaled_1e60']]
ivXs = [mp.matrix([mp.iv.mpf([x._mpi_[0], x._mpi_[1]]) for x in X[i]]) for i in range(N)]  # exact rationals as degenerate iv
# Hessian entries as intervals from degenerate endpoints (worst case wrap)
def iv_hess(f, C):
    H = mp.zeros(22, 22)
    for a in range(22):
        for b in range(a, 22):
            def at(sa, sb):
                Cv = [mp.matrix(C[k]) for k in range(N)]
                Cv[a // 2][a % 2] = Cv[a // 2][a % 2] + sa * mp.iv.mpf(HD)
                Cv[b // 2][b % 2] = Cv[b // 2][b % 2] + sb * mp.iv.mpf(HD)
                return f(Cv)
            v = (at(1, 1) - at(1, -1) - at(-1, 1) + at(-1, -1)) / (4 * mp.iv.mpf(HD) ** 2)
            H[a, b] = v
            H[b, a] = v
    return H


ivHs = [iv_hess(f, ivXs) for v, k, s, sg, f in tight]
mplam = [mp.iv.mpf([float(lamc[i]) - 1e-12, float(lamc[i]) + 1e-12]) for i in range(18)]
mplam = [x / sum(mplam) for x in mplam]
Aiv = mp.zeros(4, 4)
for p in range(4):
    for q in range(4):
        sacc = mp.iv.mpf(0)
        for i in range(18):
            for a in range(22):
                for b in range(22):
                    sacc += mplam[i] * ivHs[i][a, b] * mp.iv.mpf([float(AntiK[p][a]) - 1e-14, float(AntiK[p][a]) + 1e-14]) \
                            * mp.iv.mpf([float(AntiK[q][b]) - 1e-14, float(AntiK[q][b]) + 1e-14])
        Aiv[p, q] = (sacc + sacc) / 2
print('    interval A(lambda) - c0 I (4x4), c0 = %s :' % mp.nstr(c0, 10))
pd = True
piv = []
for k in range(4):
    p_ = Aiv[k, k] - mp.iv.mpf(c0)
    for j in range(k):
        p_ -= Aiv[k, j] ** 2 / piv[j]
    piv.append(p_)
    print('      pivot %d in [%s, %s]' % (k, mp.nstr(p_.a, 8), mp.nstr(p_.b, 8)))
    if not (p_.a > 0):
        pd = False
print('    all pivots strictly positive => A(lambda) - c0 I is PD => c_k >= %s for ALL directions'
      % mp.nstr(c0, 10) if pd else '    interval check inconclusive at dps=%d' % IVDPS)
mp.mp.dps = DPS

json.dump({'c_num_float': c_num, 'c_certified_lower': mp.nstr(c0, 12) if pd else None,
           'lambda': [mp.nstr(x, 12) for x in lamc], 'active': act,
           'pivots': [[mp.nstr(p.a, 8), mp.nstr(p.b, 8)] for p in piv]},
          open(P / 'r20_mixed_tangent_part2.json', 'w'), indent=2)
print('\nwritten r20_mixed_tangent_part1.json / part2.json')
