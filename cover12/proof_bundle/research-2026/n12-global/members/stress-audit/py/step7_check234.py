"""stress-audit step 7: independent check of lead/network_interval_certificate.py
(evidence/network-certified-234.json) - the Taylor/kappa mixed bound.

Checks
  K1  rebuild 13-face [2,3,4] network from the JSON faces + exact rational weights,
      Dirichlet pivots (their order AND a different order), q_ij >= 0
  K2  M + kappa*I full 9x9 positivity by MY LDL, plus numeric lambda_min(M)
  K3  E(theta_ref) and grad(theta_ref) recomputed with mpmath (dps=60) and compared
      with their declared intervals; trig() enclosure sanity-tested against mpmath
  K4  linear_min, max_norm2, lower bound and margin recomputed from definitions
"""
from fractions import Fraction as F
from pathlib import Path
import json, math, sys
sys.set_int_max_str_digits(10**6)
import mpmath as mp

mp.mp.dps = 60
N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
cert = json.loads((N12 / 'evidence/network-certified-234.json').read_text(encoding='utf-8'))
faces = [tuple(f) for f in cert['faces']]
alpha = [F(s) for s in cert['rational_weights']]
kappa = F(cert['kappa'])
U = F('0.361102963744508672616920293904')

out = {}
print("=== K1. rebuild network, Dirichlet pivots, conductances ===")
nsites = 1 + max(max(f) for f in faces)
nf = nsites + len(faces)
edges = []
for i in range(9):
    edges.extend([(nf + i, i), (nf + i, (i + 1) % 9)])
for i, f in enumerate(faces):
    edges.extend([(nsites + i, k) for k in f])
print(f"  nsites={nsites}  faces={len(faces)}  nf={nf}  edges={len(edges)}  weights={len(alpha)}")
assert len(edges) == len(alpha)
assert abs(sum(alpha) - 1) < F(1, 10**30)

def elim(order, label):
    """exact rational Dirichlet elimination; returns q dict and pivot list."""
    n = nf + 9
    L = [[F(0)] * n for _ in range(n)]
    for (i, k), w in zip(edges, alpha):
        L[i][i] += w; L[k][k] += w; L[i][k] -= w; L[k][i] -= w
    piv = []
    for ii, k in enumerate(order):
        p = L[k][k]
        piv.append(p)
        assert p > 0, (label, "pivot", ii, k, float(p))
        remain = order[ii + 1:] + list(range(nf, nf + 9))
        for ix_i, i in enumerate(remain):
            if L[i][k] == 0:
                continue
            for jj in remain[ix_i:]:
                L[i][jj] -= L[i][k] * L[k][jj] / p
                if jj != i:
                    L[jj][i] = L[i][jj]
    q = {}
    for i in range(9):
        for j in range(i + 1, 9):
            q[i, j] = -L[nf + i][nf + j]
    return q, piv

q, piv = elim(list(range(nf)), "their order")
q2, piv2 = elim(list(range(nf - 1, -1, -1)), "reversed order")
print(f"  their order: {len(piv)} positive pivots, min {float(min(piv)):.6e}")
print(f"  reversed order: {len(piv2)} positive pivots, min {float(min(piv2)):.6e}")
print(f"  q >= 0 : {all(v >= 0 for v in q.values())}   min q = {float(min(q.values())):.6e}")
print(f"  max |q - q_rev| = {float(max(abs(q[k] - q2[k]) for k in q)):.3e}  (order independence)")
out['K1'] = {'nf': nf, 'n_edges': len(edges), 'min_pivot_their_order': float(min(piv)),
             'min_pivot_reversed': float(min(piv2)), 'min_q': float(min(q.values())),
             'max_q_order_diff': float(max(abs(q[k] - q2[k]) for k in q))}

print("\n=== K2. M + kappa I positivity (my LDL), numeric lambda_min ===")
c = 1 - 2 * U * U
cs = {1: c}
prev, cur = F(1), c
for d in range(2, 5):
    nxt = 2 * c * cur - prev
    cs[d] = nxt; prev, cur = cur, nxt
M = [[F(0)] * 9 for _ in range(9)]
for (i, j), qq in q.items():
    v = 2 * qq * cs[min(j - i, 9 - (j - i))]
    M[i][i] += v; M[j][j] += v; M[i][j] -= v; M[j][i] -= v
rowsum = [abs(sum(M[i])) for i in range(9)]
Ms = [[M[i][j] + (kappa if i == j else F(0)) for j in range(9)] for i in range(9)]
pivM = []
Mx = [row[:] for row in Ms]
for k in range(9):
    p = Mx[k][k]; pivM.append(p)
    assert p > 0, ("M+kappaI pivot", k, float(p))
    for i in range(k + 1, 9):
        for j in range(i, 9):
            Mx[i][j] -= Mx[i][k] * Mx[k][j] / p
            Mx[j][i] = Mx[i][j]
print(f"  M*1 (exact, must be 0): max |rowsum| = {float(max(rowsum)):.3e}")
print(f"  M+kappa*I LDL pivots all > 0: {all(p > 0 for p in pivM)}  min = {float(min(pivM)):.6e}")
Mn = mp.matrix(9, 9)
for i in range(9):
    for j in range(9):
        Mn[i, j] = mp.mpf(Ms[i][j].numerator) / Ms[i][j].denominator
ev = mp.eigsy(Mn, eigvals_only=True)
evM = mp.eigsy(mp.matrix([[mp.mpf(M[i][j].numerator) / M[i][j].denominator for j in range(9)] for i in range(9)]), eigvals_only=True)
print(f"  eigenvalues of M      : {[f'{float(v):.6e}' for v in evM]}")
print(f"  eigenvalues of M+kap*I: {[f'{float(v):.6e}' for v in ev]}")
out['K2'] = {'M_rowsum_max': float(max(rowsum)), 'min_pivot_Mkappa': float(min(pivM)),
             'M_eigenvalues': [f"{float(v):.6e}" for v in evM],
             'Mkappa_eigenvalues': [f"{float(v):.6e}" for v in ev]}

print("\n=== K3. E(theta_ref), grad(theta_ref) with mpmath; trig() enclosure test ===")
yy = [F(s) for s in cert['simplex_reference']]
assert all(v >= 0 for v in yy) and sum(yy) == 1, (sum(yy),)
Lc = cert['constant_intervals']['L']; Dc = cert['constant_intervals']['D']
L_lo, L_hi = F(Lc[0]), F(Lc[1]); D_lo, D_hi = F(Dc[0]), F(Dc[1])
print(f"  their L bracket width {float(L_hi-L_lo):.3e};  D bracket [{float(D_lo):.12f},{float(D_hi):.12f}]")
mpL = 2 * mp.asin(mp.mpf(U.numerator) / U.denominator)
mpD = 9 * mpL - 2 * mp.pi
Lhi_m = mp.mpf(L_hi.numerator) / L_hi.denominator
Llo_m = mp.mpf(L_lo.numerator) / L_lo.denominator
Dhi_m = mp.mpf(D_hi.numerator) / D_hi.denominator
Dlo_m = mp.mpf(D_lo.numerator) / D_lo.denominator
print(f"  my mpmath L = {mp.nstr(mpL, 35)}   inside their bracket: {Llo_m < mpL < Lhi_m}"
      f"  (lo-diff {mp.nstr(mpL - Llo_m, 6)}, hi-diff {mp.nstr(mpL - Lhi_m, 6)})")
print(f"  my mpmath D = {mp.nstr(mpD, 35)}   inside their bracket: {Dlo_m < mpD < Dhi_m}")
yyf = [mp.mpf(v.numerator) / v.denominator for v in yy]
cum = [sum(yyf[:i]) for i in range(9)]
theta = [i * mpL - mpD * cum[i] for i in range(9)]
E = mp.mpf(0); grad = [mp.mpf(0)] * 9
for (i, j), qq in q.items():
    qf = mp.mpf(qq.numerator) / qq.denominator
    ang = theta[i] - theta[j]
    E += 2 * qf * (1 - mp.cos(ang))
    z = 2 * qf * mp.sin(ang)
    grad[i] += z; grad[j] -= z
theirE = [F(s) for s in cert['energy_at_reference']]
Elo_m = mp.mpf(theirE[0].numerator) / theirE[0].denominator
Ehi_m = mp.mpf(theirE[1].numerator) / theirE[1].denominator
print(f"  E(theta_ref): mine {mp.nstr(E, 25)}   their [{mp.nstr(Elo_m, 25)},{mp.nstr(Ehi_m, 25)}]  inside: {Elo_m < E < Ehi_m}")
print(f"  |grad|_inf = {mp.nstr(max(abs(g) for g in grad), 10)}")
# sanity of the Taylor trig enclosure used by the lead
def trig(x, kind, N=40, I=lambda a, b=None: (a if b is None else b)):
    pass
from importlib import util
spec = util.spec_from_file_location("ncert", N12 / 'lead/network_interval_certificate.py')
print("  (skipping import of lead module: needs stress_interval on path)")
worst = mp.mpf(0)
for ang in ['0.5', '1.0', '2.5', '3.14159', '6.0', '-6.28']:
    x = mp.mpf(ang)
    worst = max(worst, abs(mp.sin(x) - mp.sin(x)))  # trivial; real test below
print("  trig enclosure test needs the lead module; done separately in the note")

print("\n=== K4. linear_min, max_norm2, lower bound, margin ===")
def lin_and_norm(D, L):
    """deviation d_i = -D*(sum_{k<i} y_k - 1{k<i}); linear term and ||d||^2 on vertices."""
    lin = []
    norm2 = []
    for k in range(9):
        dev = [D * (sum(yy[:i]) - (1 if k < i else 0)) for i in range(9)]
        lin.append(sum((g * d for g, d in zip(grad, dev)), mp.mpf(0)))
        norm2.append(sum(d * d for d in dev))
    return min(lin), max(norm2)
lmin, mnorm = lin_and_norm(mpD, mpL)
lm_m = mp.mpf(F(cert['linear_min'][0]).numerator) / F(cert['linear_min'][0]).denominator
lm_h = mp.mpf(F(cert['linear_min'][1]).numerator) / F(cert['linear_min'][1]).denominator
mn_m = mp.mpf(F(cert['max_norm2'][0]).numerator) / F(cert['max_norm2'][0]).denominator
mn_h = mp.mpf(F(cert['max_norm2'][1]).numerator) / F(cert['max_norm2'][1]).denominator
print(f"  my linear min = {mp.nstr(lmin, 20)}   their [{mp.nstr(lm_m, 20)},{mp.nstr(lm_h, 20)}]  inside: {lm_m < lmin < lm_h}")
print(f"  my max_norm2  = {mp.nstr(mnorm, 20)}   their [{mp.nstr(mn_m, 20)},{mp.nstr(mn_h, 20)}]  inside: {mn_m < mnorm < mn_h}")
lower = E + lmin - mp.mpf(kappa.numerator) / kappa.denominator * mnorm / 2
U2m = mp.mpf(U.numerator) / U.denominator
U2 = U2m * U2m
their_low = [F(s) for s in cert['lower_energy']]
low_m = mp.mpf(their_low[0].numerator) / their_low[0].denominator
low_h = mp.mpf(their_low[1].numerator) / their_low[1].denominator
print(f"  my lower bound = {mp.nstr(lower, 25)}   their [{mp.nstr(low_m, 25)},{mp.nstr(low_h, 25)}]  inside: {low_m < lower < low_h}")
print(f"  U^2 = {mp.nstr(U2, 30)}")
their_margin = F(cert['margin_lower'])
my_margin = lower - U2
print(f"  my margin = {mp.nstr(my_margin, 12)}   their margin = {mp.nstr(mp.mpf(their_margin.numerator)/their_margin.denominator, 12)}")

print("\n=== K5. lead trig() enclosure at their own L endpoints (mpmath comparison) ===")
sys.path.insert(0, str(N12 / 'lead'))
import network_interval_certificate as NC
for nm, x in (("lo/2", Lb[0] / 2), ("hi/2", Lb[1] / 2)):
    t = NC.trig(x, 'sin')
    tl = mp.mpf(t.lo.numerator) / t.lo.denominator
    th = mp.mpf(t.hi.numerator) / t.hi.denominator
    true = mp.sin(mp.mpf(x.numerator) / x.denominator)
    print(f"  trig({nm},'sin') = [{mp.nstr(tl, 25)}, {mp.nstr(th, 25)}]  contains true: {tl <= true <= th}"
          f"   hi<U: {th < U2m if False else th < mp.mpf(U.numerator)/U.denominator}")
print("  => assertion trig(lo/2).hi < U < trig(hi/2).lo :",
      mp.mpf(NC.trig(Lb[0] / 2, 'sin').hi.numerator) / NC.trig(Lb[0] / 2, 'sin').hi.denominator < mp.mpf(U.numerator) / U.denominator
      < mp.mpf(NC.trig(Lb[1] / 2, 'sin').lo.numerator) / NC.trig(Lb[1] / 2, 'sin').lo.denominator)
out['K3_K4'] = {'E_mine': mp.nstr(E, 25), 'grad_inf': mp.nstr(max(abs(g) for g in grad), 12),
                'linear_min_mine': mp.nstr(lmin, 20), 'max_norm2_mine': mp.nstr(mnorm, 20),
                'lower_mine': mp.nstr(lower, 25), 'U2_mine': mp.nstr(U2, 25),
                'margin_mine': mp.nstr(lower - U2, 12), 'margin_theirs': str(their_margin),
                'E_inside_their_interval': bool(float(theirE[0]) < float(E) < float(theirE[1])),
                'lower_inside_their_interval': bool(float(their_low[0]) < float(lower) < float(their_low[1])),
                'L_inside_their_bracket': bool(float(L_lo) < float(mpL) < float(L_hi)),
                'D_inside_their_bracket': bool(float(D_lo) < float(mpD) < float(D_hi))}

(N12 / 'members/stress-audit/evidence/stress-audit-234check.json').write_text(json.dumps(out, indent=1), encoding='utf-8')
print("\nwrote evidence/stress-audit-234check.json")
