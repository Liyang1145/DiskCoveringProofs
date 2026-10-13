"""stress-audit step 13: sweep all evidence/network-certified-*.json
Same independent checks as step 7 (network rebuild, Dirichlet pivots in both orders,
q>=0, M*1=0, M+kappa*I LDL, numeric lambda_min(M), and full recomputation of
E(theta_ref), linear_min, max||d||^2, lower, margin vs the recorded values).
"""
from fractions import Fraction as F
from pathlib import Path
import json, sys
sys.set_int_max_str_digits(10**6)
import mpmath as mp

mp.mp.dps = 60
N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
U = F('0.361102963744508672616920293904')
Um = mp.mpf(U.numerator) / U.denominator
U2 = Um * Um
rows = []
print(f"{'net':>9} {'edges':>5} {'kappa':>8} {'minpiv1':>10} {'minpiv2':>10} {'minq':>10} {'lam_min(M)':>11} "
      f"{'lam+kap':>10} {'M+kap>0':>8} {'dE':>9} {'dlow':>9} {'margin':>12} {'all':>5}")
for f in sorted(N12.glob('evidence/network-certified-*.json')):
    name = f.stem.replace('network-certified-', '')
    cert = json.loads(f.read_text(encoding='utf-8'))
    faces = [tuple(x) for x in cert['faces']]
    alpha = [F(s) for s in cert['rational_weights']]
    kappa = F(cert['kappa'])
    nsites = 1 + max(max(x) for x in faces)
    nf = nsites + len(faces)
    edges = []
    for i in range(9):
        edges.extend([(nf + i, i), (nf + i, (i + 1) % 9)])
    for i, fc in enumerate(faces):
        edges.extend([(nsites + i, k) for k in fc])

    def elim(order):
        n = nf + 9
        L = [[F(0)] * n for _ in range(n)]
        for (i, k), w in zip(edges, alpha):
            L[i][i] += w; L[k][k] += w; L[i][k] -= w; L[k][i] -= w
        piv = []
        for ii, k in enumerate(order):
            p = L[k][k]; piv.append(p)
            if p <= 0:
                return None, None
            remain = order[ii + 1:] + list(range(nf, nf + 9))
            for ix_i, i in enumerate(remain):
                if L[i][k] == 0:
                    continue
                for jj in remain[ix_i:]:
                    L[i][jj] -= L[i][k] * L[k][jj] / p
                    if jj != i:
                        L[jj][i] = L[i][jj]
        q = {(i, j): -L[nf + i][nf + j] for i in range(9) for j in range(i + 1, 9)}
        return q, piv

    q, piv1 = elim(list(range(nf)))
    q2, piv2 = elim(list(range(nf - 1, -1, -1)))
    ok = True
    if q is None or q2 is None or any(v < 0 for v in q.values()):
        ok = False
        minq = float('nan')
    else:
        minq = float(min(q.values()))
    c = 1 - 2 * U * U
    cs = {1: c}; prev, cur = F(1), c
    for d in range(2, 5):
        nxt = 2 * c * cur - prev; cs[d] = nxt; prev, cur = cur, nxt
    M = [[F(0)] * 9 for _ in range(9)]
    for (i, j), qq in q.items():
        v = 2 * qq * cs[min(j - i, 9 - (j - i))]
        M[i][i] += v; M[j][j] += v; M[i][j] -= v; M[j][i] -= v
    rowsum = max(abs(sum(M[i])) for i in range(9))
    Ms = [[M[i][j] + (kappa if i == j else F(0)) for j in range(9)] for i in range(9)]
    Mx = [r[:] for r in Ms]; pivM = []
    try:
        for k in range(9):
            p = Mx[k][k]; pivM.append(p)
            assert p > 0
            for i in range(k + 1, 9):
                for j in range(i, 9):
                    Mx[i][j] -= Mx[i][k] * Mx[k][j] / p; Mx[j][i] = Mx[i][j]
        mkap = True
    except AssertionError:
        mkap = False
    lam = mp.eigsy(mp.matrix([[mp.mpf(M[i][j].numerator) / M[i][j].denominator for j in range(9)] for i in range(9)]), eigvals_only=True)

    # recompute E, gradient, linear min, max norm^2 at the recorded reference
    yy = [F(s) for s in cert['simplex_reference']]
    ysol = sum(yy) == 1 and all(v >= 0 for v in yy)
    Lb = [F(s) for s in cert['constant_intervals']['L']]
    mpL = 2 * mp.asin(Um); mpD = 9 * mpL - 2 * mp.pi
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
    lin = []; nrm = []
    for k in range(9):
        dev = [mpD * (sum(yyf[:i]) - (1 if k < i else 0)) for i in range(9)]
        lin.append(sum((g * d for g, d in zip(grad, dev)), mp.mpf(0)))
        nrm.append(sum(d * d for d in dev))
    lower = E + min(lin) - mp.mpf(kappa.numerator) / kappa.denominator * max(nrm) / 2
    def as_mp(s):
        v = F(s); return mp.mpf(v.numerator) / v.denominator
    dE = mp.nstr(abs(E - as_mp(cert['energy_at_reference'][0])), 3)
    dL = mp.nstr(abs(lower - as_mp(cert['lower_energy'][0])), 3)
    margin = lower - U2
    lmin = float(min(lam))
    allok = (ok and mkap and rowsum == 0 and ysol and lmin > -float(kappa)
             and abs(E - as_mp(cert['energy_at_reference'][0])) < mp.mpf('1e-25')
             and abs(lower - as_mp(cert['lower_energy'][0])) < mp.mpf('1e-25') and margin > 0)
    rows.append((name, len(edges), float(kappa), float(min(piv1)), float(min(piv2)), minq, lmin, mkap, dE, dL,
                 mp.nstr(margin, 8), allok))
    print(f"{name:>9} {len(edges):>5} {float(kappa):>8.4f} {float(min(piv1)):>10.3e} {float(min(piv2)):>10.3e} {minq:>10.3e} "
          f"{lmin:>11.4e} {lmin + float(kappa):>10.4e} {str(mkap):>8} {dE:>9} {dL:>9} {mp.nstr(margin, 8):>12} {str(allok):>5}")

print("\nlegend: kappa per network from its own JSON; lam_min(M) must be > -kappa (column 'lam+kap' > 0);")
print("        E/low diffs vs recorded intervals; margin = lower - U^2 must be > 0.")
N12.joinpath('members/stress-audit/evidence/stress-audit-network-sweep.json').write_text(
    json.dumps([{'net': r[0], 'edges': r[1], 'min_pivot_order': r[2], 'min_pivot_reversed': r[3],
                 'min_q': r[4], 'lam_min_M': r[5], 'Mkappa_pivots_positive': r[6],
                 'abs_diff_E': r[7], 'abs_diff_lower': r[8], 'margin': r[9], 'all_checks': r[10]} for r in rows], indent=1),
    encoding='utf-8')
print("\nwrote evidence/stress-audit-network-sweep.json")
