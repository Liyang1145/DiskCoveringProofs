"""R20-AH: the margin LP, properly formulated (bounded, with Farkas output).

The system: find z with |z|_inf <= 1 satisfying the affine KKT rows of the candidate and beating
every sampled tuple of every factor:
        (VALID)   (a_k(pi*) - a_k(X)) . z  >=  b_k(X) - b_k(pi*)      for all samples X,
        (KKT)     bp[r] + B[r] . z = 0   (interior),  >= 0 (upper boundary),  <= 0 (lower)
The margin s* = max over z of the minimum VALID slack is the honest measure; s* < 0 certifies
that the pure 29-factor family cannot make the candidate a simultaneous maximum at R = r_cand.

Reported: s*, the LP dual (Farkas) multipliers with provenance, and the two sanity controls on the
saved dual z_c825 (which hits pi exactly at the candidate but is beaten on 5 samples).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_margin78.py
"""
import json, math, sys
import numpy as np
from pathlib import Path
from scipy.optimize import linprog

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_family78 import load_candidate, lin_form, const_of, param_table
from r20_lp78 import sample_tuples, cone_variant


def build(npts, seed):
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B = np.load(HERE / 'r20_B78.npy'); bp = np.load(HERE / 'r20_bp78.npy')
    tab = param_table(p0)
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    S = sample_tuples(C, p0, npts, seed)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]; kv[j] = int(k)
    Aeq = []; beq = []; Aub = []; bub = []; prov = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q]); prov.append(('eq', r['name']))
        elif r['activity'] == 'up':
            Aub.append(-B[q]); bub.append(bp[q]); prov.append(('up', r['name']))
        else:
            Aub.append(B[q]); bub.append(-bp[q]); prov.append(('lo', r['name']))
    return dict(C=C, p0=p0, R=R, Rv=Rv, bv=bv, kv=kv, Aeq=np.array(Aeq), beq=np.array(beq),
                Aub=np.array(Aub), bub=np.array(bub), prov=prov, tab=tab, a_c=a_c, b_c=b_c)


def margin_lp(d, use_cone=0, use_kkt=True):
    Rv, bv = d['Rv'], d['bv']
    nv = NZ + 1
    rows = []; rhs = []; prov = []
    for j in range(len(bv)):
        r = np.zeros(nv); r[:NZ] = -Rv[j]; r[NZ] = -1.0
        rows.append(r); rhs.append(-bv[j]); prov.append(('VAL', int(d['kv'][j])))
    if use_kkt:
        for j in range(d['Aub'].shape[0]):
            r = np.zeros(nv); r[:NZ] = d['Aub'][j]; rows.append(r); rhs.append(d['bub'][j])
            prov.append(('kkt1', d['prov'][j][1]))
    if use_cone:
        cA, cprov = cone_variant(use_cone)
        for j in range(cA.shape[0]):
            r = np.zeros(nv); r[:NZ] = cA[j]; rows.append(r); rhs.append(0.0)
            prov.append(('cone', cprov[j]))
    rows = np.array(rows); rhs = np.array(rhs)
    Aeq = np.hstack([d['Aeq'], np.zeros((d['Aeq'].shape[0], 1))]) if use_kkt else None
    beq = d['beq'] if use_kkt else None
    c = np.zeros(nv); c[NZ] = -1.0
    res = linprog(c, A_ub=rows, b_ub=rhs, A_eq=Aeq, b_eq=beq,
                  bounds=[(-1, 1)] * NZ + [(None, None)], method='highs')
    return res, rows, rhs, prov


def main():
    print('=== R20-AH: margin LP on the 78-parameter family, R = r_cand ===')
    for npts, seed in [(300, 13), (1000, 31)]:
        d = build(npts, seed)
        for tag, cv in [('VAL+KKT', 0), ('VAL+KKT+cone', 3)]:
            res, rows, rhs, prov = margin_lp(d, use_cone=cv)
            s = res.x[NZ] if res.status == 0 else float('nan')
            print('  npts=%4d %-13s: s* = %+.6e   (s*<0 => the family CANNOT make the candidate'
                  ' a simultaneous maximum)' % (npts, tag, s))
            if res.status == 0 and s < 0:
                lam = -np.asarray(res.ineqlin.marginals)
                F = lam @ rows
                print('      Farkas: nonneg lam %s, rows used %d, |sum lam A| on z = %.2e,'
                      ' lam.rhs = %+.4e' % (bool(lam.min() > -1e-9), int((lam > 1e-9).sum()),
                                            np.abs(F[:NZ]).max(), float(lam @ rhs)))
                cnt = {}
                for j in np.where(lam > 1e-9)[0]:
                    t = prov[j][0]; cnt[t] = cnt.get(t, 0) + 1
                print('      provenance: %s' % cnt)
        # controls
        zc = np.array([float(f'{v:.9f}') for v in
                       json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
        sl = d['Rv'] @ zc - d['bv']
        print('  control z_c825: min VAL slack = %+.4e (beaten at %d samples); V(pi*)=%.9f'
              % (sl.min(), int((sl < 0).sum()),
                 const_of(zc, d['R']) + sum(d['b_c'][k] + d['a_c'][k] @ zc for k in range(29))))


if __name__ == '__main__':
    main()
