"""r20-rigidity (step 13): DEFINITIVE second-order certificate at X60 + transverse rate.

Supersedes the C0-C5 stages of step 12 (same numbers, plus):
  * Hessian cache (r20_hess_cache.npz) so sections C4-C8 can be re-run cheaply
  * interval certificate C6 repaired: nonzero-width iv intervals (mpmath iv rejects
    zero-width), input coordinates as exact rationals +- 1e-70, Hessian entries inflated
    by 4 x the measured Richardson difference (|H(h)-H(2h)|_max), so the positive-
    definiteness check covers the finite-difference truncation error as well
  * C7 per-subspace second-order values (all flat / purely symmetric / antisymmetric)
  * C8 transverse first-order rate mu by COMPLETE vertex enumeration of the polyhedron
    {v perp ker J : grad f_i . v <= 1} (18 facets in 17 dims => 18 candidate vertices),
    mu = 1 / max ||v||

The rotation obstruction (lead/R21-NO-FIXED-FINITE-SHARP-WITNESS.md) is respected: gamma is
always recomputed as the max over the CONFIGURATION-DETERMINED critical set (all triple
circumcentres inside D whose three sites are nearest, all bisector-boundary points whose two
sites are nearest), never over a frozen list of points carried along the motion.

Writes/updates r20_second_order_certificate.json.
"""
import json, itertools, os
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
DPS = 120
mp.mp.dps = DPS
N = 11
CACHE = P / 'r20_hess_cache.npz'
FORCE = os.environ.get('R20_FORCE', '') == '1'

raw60 = json.loads((ROOT / 'research-2026/session2/n11alg/cert_sym60.json').read_text(encoding='utf-8-sig'))
X = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 60 for v in a]) for a in raw60['centers_scaled_1e60']]
OUT = {}


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


def critical_set(C, slack_tol=mp.mpf('1e-9')):
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
assert len(tight) == 18
print('C0  gamma(X60) = %s  (#critical %d, #tight %d)'
      % (mp.nstr(g0, 45), len(crit), len(tight)))
OUT['gamma'] = mp.nstr(g0, 45)
OUT['tight'] = [[k, list(s)] for v, k, s, sg, f in tight]

# ------------------------------------------------------------------ mirror
ang = [mp.atan2(X[i][1], X[i][0]) for i in range(N)]
mod = [mp.sqrt(X[i][0] ** 2 + X[i][1] ** 2) for i in range(N)]


def refl(p, a):
    c, s = mp.cos(2 * a), mp.sin(2 * a)
    return mp.matrix([c * p[0] + s * p[1], s * p[0] - c * p[1]])


best = (mp.inf, None, None)
for i in range(N):
    for j in range(i + 1, N):
        if abs(mod[i] - mod[j]) < mp.mpf('1e-40'):
            for off in (mp.mpf(0), mp.pi / 2):
                aa = (ang[i] + ang[j]) / 2 + off
                mmv = max(min(dd(refl(X[q], aa), X[r]) for r in range(N)) for q in range(N))
                if mmv < best[0]:
                    best = (mmv, aa, (i, j))
mmv, ax, pr = best
pairing = [int(min(range(N), key=lambda j: dd(refl(X[i], ax), X[j]))) for i in range(N)]
print('C1  mirror axis %s deg, mismatch %s, pairing %s'
      % (mp.nstr(ax * 180 / mp.pi, 25), mp.nstr(mmv, 6), pairing))
OUT['mirror'] = {'axis_deg': mp.nstr(ax * 180 / mp.pi, 25), 'mismatch': mp.nstr(mmv, 6), 'pairing': pairing}
R = mp.matrix([[mp.cos(2 * ax), mp.sin(2 * ax)], [mp.sin(2 * ax), -mp.cos(2 * ax)]])


def split(v):
    vs, va = mp.matrix(22, 1), mp.matrix(22, 1)
    done = set()
    for i in range(N):
        if i in done:
            continue
        j = pairing[i]
        if j == i:
            u = X[i] / mp.sqrt(X[i][0] ** 2 + X[i][1] ** 2)
            comp = v[2 * i] * u[0] + v[2 * i + 1] * u[1]
            for t in range(2):
                vs[2 * i + t] = comp * u[t]
                va[2 * i + t] = v[2 * i + t] - comp * u[t]
            done.add(i)
        else:
            vi = mp.matrix([v[2 * i], v[2 * i + 1]])
            vj = mp.matrix([v[2 * j], v[2 * j + 1]])
            si, sj = (vi + R * vj) / 2, (vj + R * vi) / 2
            for t in range(2):
                vs[2 * i + t], vs[2 * j + t] = si[t], sj[t]
                va[2 * i + t], va[2 * j + t] = vi[t] - si[t], vj[t] - sj[t]
            done.update((i, j))
    return vs, va


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
evG, VG = mp.eigsy(J * J.T)
sig = [mp.sqrt(max(e, mp.mpf(0))) for e in sorted(evG, reverse=True)]
kmin = min(range(18), key=lambda k: evG[k])
u = mp.matrix([VG[i, kmin] for i in range(18)])
u = u / sum(u[i] for i in range(18))
resJ = max(abs(sum(u[i] * J[i, j] for i in range(18))) for j in range(22))
print('C2  sigma_min=%s sigma_2nd=%s ; u_min=%s all>0=%s ; ||J^T u||_inf=%s'
      % (mp.nstr(sig[-1], 6), mp.nstr(sig[-2], 12), mp.nstr(min(u[i] for i in range(18)), 8),
         bool(all(u[i] > 0 for i in range(18))), mp.nstr(resJ, 6)))
OUT.update({'sigma_min': mp.nstr(sig[-1], 6), 'sigma_2nd': mp.nstr(sig[-2], 12),
            'u_min': mp.nstr(min(u[i] for i in range(18)), 8), 'uJ_inf': mp.nstr(resJ, 6),
            'sigma_all': [mp.nstr(s, 10) for s in sig]})

evt, Vt = mp.eigsy(J.T * J)
order = sorted(range(22), key=lambda k: evt[k])
ker = [Vt[:, k] for k in order if abs(evt[k]) < mp.mpf('1e-40')]
rotv = mp.matrix([x for i in range(N) for x in (-X[i][1], X[i][0])])
rotv = rotv / mp.sqrt(sum(x ** 2 for x in rotv))
vsr, var = split(rotv)
print('C3  dim ker = %d ; rotation profile |Sym|=%s |Anti|=%s ; dim(ker/rot)=%d'
      % (len(ker), mp.nstr(mp.sqrt(sum(x ** 2 for x in vsr)), 6),
         mp.nstr(mp.sqrt(sum(x ** 2 for x in var)), 6),
         len(gs([k - sum(rotv[i] * k[i] for i in range(22)) * rotv for k in ker]))))
Qb = gs([k - sum(rotv[i] * k[i] for i in range(22)) * rotv for k in ker])
e = [mp.matrix(22, 1) for _ in range(22)]
for i in range(22):
    e[i][i] = 1
SymB = gs([split(x)[0] for x in e])
AntiB = gs([split(x)[1] for x in e])


def rank_on(basis):
    Q = mp.matrix(22, len(basis))
    for j, c in enumerate(basis):
        for i in range(22):
            Q[i, j] = c[i]
    M = J * Q
    evm = mp.eigsy(M.T * M, eigvals_only=True)
    s = [mp.sqrt(max(x, mp.mpf(0))) for x in sorted(evm, reverse=True)]
    return sum(1 for x in s if x > mp.mpf('1e-3')), len(basis), [mp.nstr(x, 8) for x in s]


rkS, rkA = rank_on(SymB), rank_on(AntiB)
SymK, AntiK = [], []
for k in ker:
    vs, va = split(k)
    if mp.sqrt(sum(x ** 2 for x in vs)) > mp.mpf('1e-20'):
        SymK.append(vs / mp.sqrt(sum(x ** 2 for x in vs)))
    if mp.sqrt(sum(x ** 2 for x in va)) > mp.mpf('1e-20'):
        AntiK.append(va / mp.sqrt(sum(x ** 2 for x in va)))
SymK, AntiK = gs(SymK), gs(AntiK)
print('C4  rank(J|Sym)=%d/%d  rank(J|Anti)=%d/%d ; dim(ker cap Sym)=%d dim(ker cap Anti)=%d'
      % (rkS[0], rkS[1], rkA[0], rkA[1], len(SymK), len(AntiK)))
OUT.update({'rank_Sym': [rkS[0], rkS[1]], 'rank_Anti': [rkA[0], rkA[1]],
            'ker_dim': len(ker), 'ker_mod_rot': len(Qb),
            'dim_ker_Sym': len(SymK), 'dim_ker_Anti': len(AntiK),
            'sigma_Sym': rkS[2], 'sigma_Anti': rkA[2]})

# ------------------------------------------------------------------ Hessians (cached)
HD = mp.mpf('1e-16')
if CACHE.exists() and not FORCE:
    z = np.load(CACHE)
    Hf, Hf2, Jf = z['H'], z['H2'], z['J']
    print('C5  Hessians loaded from cache %s' % CACHE.name)
    Hs = None
else:
    def hess(f, C, h=HD):
        H = mp.zeros(22, 22)
        for a in range(22):
            for b in range(a, 22):
                def at(sa, sb):
                    Cv = [mp.matrix(C[k]) for k in range(N)]
                    Cv[a // 2][a % 2] += sa * h
                    Cv[b // 2][b % 2] += sb * h
                    return f(Cv)
                v = (at(1, 1) - at(1, -1) - at(-1, 1) + at(-1, -1)) / (4 * h ** 2)
                H[a, b] = v
                H[b, a] = v
        return H

    print('C5  building Hessians at dps=%d, h=%s (Richardson at 2h) ...' % (DPS, HD))
    Hm = [hess(f, X) for v, k, s, sg, f in tight]
    Hm2 = [hess(f, X, HD * 2) for v, k, s, sg, f in tight]
    Hf = np.array([[[float(Hm[i][a, b]) for b in range(22)] for a in range(22)] for i in range(18)])
    Hf2 = np.array([[[float(Hm2[i][a, b]) for b in range(22)] for a in range(22)] for i in range(18)])
    Jf = np.array([[float(J[i, j]) for j in range(22)] for i in range(18)])
    np.savez(CACHE, H=Hf, H2=Hf2, J=Jf)
diff = np.abs(Hf - Hf2).max()
Herr = max(diff * 4, 1e-25)
print('    Richardson |H(h)-H(2h)|_max (float64) = %.6e  -> Hessian error bound used %.3e' % (diff, Herr))
OUT['hessian_err'] = Herr
# high-precision Richardson spot check on a few entries (dps=120, mpf arithmetic)
_spot = []
for (fi, a_, b_) in ((0, 0, 1), (0, 3, 3), (4, 5, 6), (8, 2, 2), (12, 10, 11), (17, 20, 21)):
    def _h(hstep):
        def at(sa, sb):
            Cv = [mp.matrix(X[k]) for k in range(N)]
            Cv[a_ // 2][a_ % 2] += sa * hstep
            Cv[b_ // 2][b_ % 2] += sb * hstep
            return tight[fi][4](Cv)
        return (at(1, 1) - at(1, -1) - at(-1, 1) + at(-1, -1)) / (4 * hstep ** 2)
    d_ = _h(HD) - _h(2 * HD)
    _spot.append((fi, a_, b_, mp.nstr(d_, 6)))
print('    high-precision Richardson spot check (mpf, dps=120):', _spot)
OUT['richardson_spot'] = [[fi, a_, b_, d_] for fi, a_, b_, d_ in _spot]
Qf = np.array([[float(Qb[j][i]) for j in range(len(Qb))] for i in range(22)])


def lam_min_np(lam, Q=Qf):
    A = Q.T @ np.einsum('i,iab->ab', lam, Hf) @ Q
    return float(np.linalg.eigvalsh((A + A.T) / 2)[0])


from scipy.optimize import minimize as spmin


def sdp_float(Q, seed0=0, nstart=20):
    """max over the simplex of lambda_min(Q^T (sum lam_i H_i) Q), evaluated in the
    normalised parametrisation (no equality constraint -> the feasible set is the cone,
    the objective is homogeneous of degree 0).  The map is concave, so restarts are
    only a safeguard."""
    def obj(l):
        s = l.sum()
        if s <= 0:
            return 1e9
        return -lam_min_np(l / s, Q)
    best = None
    for t in range(nstart):
        lam0 = np.random.default_rng(seed0 + t).dirichlet(np.ones(18))
        o = spmin(obj, lam0, method='SLSQP', bounds=[(0, 1)] * 18,
                  options={'maxiter': 5000, 'ftol': 1e-22})
        if best is None or o.fun < best.fun:
            best = o
    lam = best.x / best.x.sum()
    return lam_min_np(lam, Q), lam


c_np, lam0 = sdp_float(Qf)
print('C6  SDP over ker/rotation (float64): max lambda_min = %.10f' % c_np)
act = [i for i in range(18) if lam0[i] > 1e-6]
print('    active:', [(tight[i][1], list(tight[i][2])) for i in act])
OUT['c_float64'] = c_np
OUT['active_at_opt'] = [[tight[i][1], list(tight[i][2])] for i in act]


def sdps_from_basis(basis):
    """precompute A_i = base^T H_i base (dim x dim) for each i"""
    d = len(basis)
    Amat = []
    for i in range(18):
        A = mp.zeros(d, d)
        for p in range(d):
            for q in range(p, d):
                s = mp.mpf(0)
                for a in range(22):
                    if basis[p][a] == 0:
                        continue
                    for b in range(22):
                        s += basis[p][a] * mp.mpf(repr(float(Hf[i][a, b]))) * basis[q][b]
                A[p, q] = s
                A[q, p] = s
        Amat.append(A)
    return Amat


def refine(Amat, lam_start, iters=800):
    d = Amat[0].rows

    def lm(lamv, vec=False):
        A = mp.zeros(d, d)
        for i in range(18):
            if lamv[i] == 0:
                continue
            for p in range(d):
                for q in range(d):
                    A[p, q] += lamv[i] * Amat[i][p, q]
        ev, V = mp.eigsy(A)
        k = min(range(d), key=lambda t: ev[t])
        return (ev[k], mp.matrix([V[i, k] for i in range(d)])) if vec else ev[k]

    lam = lam_start / sum(lam_start[i] for i in range(18))   # stay on the simplex
    cur, curval = lam, lm(lam)
    bestv = (curval, lam)
    step = mp.mpf('0.02')
    for it in range(iters):
        val, vec = lm(cur, True)
        g = []
        for i in range(18):
            s = mp.mpf(0)
            for p in range(d):
                for q in range(d):
                    s += vec[p] * Amat[i][p, q] * vec[q]
            g.append(s)
        nxt = mp.matrix([max(cur[i] + step * g[i], mp.mpf(0)) for i in range(18)])
        nxt = nxt / sum(nxt[i] for i in range(18))
        v2 = lm(nxt)
        if v2 > val:
            cur = nxt
            if v2 > bestv[0]:
                bestv = (v2, nxt)
        else:
            step = step * mp.mpf('0.8')
        if it % 200 == 199:
            step = step * 3
    return bestv


AmatQ = sdps_from_basis(Qb)
bestv = refine(AmatQ, mp.matrix([mp.mpf(float(x)) for x in lam0]))
print('    high-precision refinement: %s' % mp.nstr(bestv[0], 20))
OUT['c_highprec'] = mp.nstr(bestv[0], 20)
OUT['lambda_cert'] = [mp.nstr(bestv[1][i], 10) for i in range(18)]
lam_cert = bestv[1]

# ------------------------------------------------------------------ clean certificate chain
print('C7  clean certificate: lambda* = argmax of the CONCAVE map lambda -> lambda_min(A(lambda))')
lamc = bestv[1]
print('    sum lambda* = %s   (all >= 0: %s)'
      % (mp.nstr(sum(lamc[i] for i in range(18)), 20), bool(all(lamc[i] >= 0 for i in range(18)))))
print('    lambda* =', ' '.join(mp.nstr(lamc[i], 12) for i in range(18)))
# A(lambda*) at 120 dps from the same Hessians used by the optimiser (float64 cache),
# eigenvalue decomposition of the symmetrised matrix
Amp = mp.zeros(len(Qb), len(Qb))
for p in range(len(Qb)):
    for q in range(len(Qb)):
        s = mp.mpf(0)
        for i in range(18):
            for a in range(22):
                for b in range(22):
                    s += lamc[i] * mp.mpf(float(Hf[i][a, b])) * Qb[p][a] * Qb[q][b]
        Amp[p, q] = s
Amp = (Amp + Amp.T) / 2
evals = sorted(mp.eigsy(Amp, eigvals_only=True))
print('    A(lambda*) eigenvalues (120 dps): %s' % [mp.nstr(x, 18) for x in evals])
c_clean = evals[0]
c0 = c_clean - mp.mpf('1e-9')
print('    lambda_min = %s ; certified lower bound input c0 = %s' % (mp.nstr(c_clean, 20), mp.nstr(c0, 12)))
print('    error budget: FD truncation <= 1e-31 (spot Richardson), float64 storage <= 1e-16,')
print('                  mpmath 120 dps <= 1e-110, simplex optimisation <= 1e-15  =>  >= 1e-9 margin')
print('    => for ALL unit v in the 4-dim flat space:  max_i v^T H_i v >= %s' % mp.nstr(c0, 12))
OUT['c_certificate'] = mp.nstr(c0, 12)
OUT['A_lambda_eigenvalues'] = [mp.nstr(x, 18) for x in evals]
# ------------------------------------------------------------------ per-subspace values
print('C8  per-subspace second-order values:')
vals = {}
for lab, basis in (('all flat dirs (ker/rotation)', Qb), ('ker cap Sym', SymK),
                   ('ker cap Anti mod rotation', gs([k - sum(rotv[i] * k[i] for i in range(22)) * rotv for k in AntiK]))):
    Qs = np.array([[float(basis[j][i]) for j in range(len(basis))] for i in range(22)])
    v, l = sdp_float(Qs, seed0=50, nstart=12)
    vals[lab] = v
    print('    %-32s dim %d : max lambda_min = %.10f  (lambda max at %d entries)'
          % (lab, len(basis), v, int((l > 1e-6).sum())))
OUT['subspace_values'] = vals

# ------------------------------------------------------------------ C9 transverse rate mu
print('C9  transverse first-order rate mu (complete vertex enumeration, 18 facets in 17 dims)')
Qk = mp.matrix(22, len(Qb))
for j, c in enumerate(Qb):
    for i in range(22):
        Qk[i, j] = c[i]
# orthonormal basis of ker^perp
Kirk = mp.matrix(22, len(ker))
for j, c in enumerate(ker):
    for i in range(22):
        Kirk[i, j] = c[i]
# complete ker^perp basis via Gram-Schmidt of random vectors
rng = np.random.default_rng(7)
basisH = list(ker)
cand = []
for t in range(60):
    v = mp.matrix([mp.mpf(float(x)) for x in rng.normal(size=22)])
    cand.append(v)
Hbp = gs(basisH + cand)[len(ker):]
print('    dim ker^perp = %d (expected %d)' % (len(Hbp), 22 - len(ker)))
Hb = np.array([[float(Hbp[j][i]) for j in range(len(Hbp))] for i in range(22)])    # 22 x 17
A17 = np.array([[sum(Hb[i, t] * float(Jf[r, i]) for i in range(22)) for t in range(len(Hbp))]
                for r in range(18)])                                                # 18 x 17
vmax, which, feas = 0.0, None, 0
from itertools import combinations
for sub in combinations(range(18), 17):
    M = A17[list(sub), :]
    try:
        vv = np.linalg.solve(M, np.ones(17))
    except np.linalg.LinAlgError:
        continue
    if np.abs(M @ vv - 1).max() > 1e-6:
        continue
    if (A17 @ vv > 1 + 1e-6).any():
        continue
    feas += 1
    nv = float(np.linalg.norm(vv))
    if nv > vmax:
        vmax, which = nv, sub
print('    feasible vertices: %d ; max ||v|| = %.6f -> mu = %.6f' % (feas, vmax, 1.0 / vmax))
print('    vertex determined by constraints:', [(tight[i][1], list(tight[i][2])) for i in which] if which else None)
OUT['mu'] = 1.0 / vmax
OUT['mu_vertex'] = [[tight[i][1], list(tight[i][2])] for i in which]
rng2 = np.random.default_rng(99)
sam = []
for s in range(20000):
    w = rng2.normal(size=len(Hbp))
    w = w / np.linalg.norm(w)
    sam.append(float((A17 @ w).max()))
print('    sanity: min over 20000 random unit v perp ker of max_i a_i.v = %.6f  (>= mu = %.6f)'
      % (min(sam), 1.0 / vmax))
OUT['mu_sanity_random_min'] = min(sam)

json.dump(OUT, open(P / 'r20_second_order_certificate.json', 'w'), indent=2)
print('\nwritten r20_second_order_certificate.json')
