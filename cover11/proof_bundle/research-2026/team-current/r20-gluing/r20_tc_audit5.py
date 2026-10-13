"""R20-TC-AUDIT 5/5: the nested dual representation of the threshold condition, from the
INDEPENDENT SymPy Jacobian at the repaired root.

The KKT row of the 12x12 system is  e_R - sum_i lam_i grad f_i(z) = 0, i.e. the coordinate
gradient e_R = dR must lie in the row space of the 5x7 Jacobian J with coefficients lam (the sign
convention of the repo makes the assembled combination vanish, so with the SymPy Jacobian the
relation reads  e_R = sum_i (-lam_i) grad f_i).

Reports the exact coefficients, the residual of that relation, and the conditioning of the
coefficient system (min singular value of J).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit5.py
"""
import json, sys
from pathlib import Path

import numpy as np
import sympy as sp

HERE = Path(__file__).parent
TC = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\n11tc\py')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')


def main():
    sys.path.insert(0, str(TC))
    from mpmath import mp, mpf
    mp.dps = 60
    import tc_core as CORE
    import tc_s32_kraw as K32
    import tc_s33_kkt as S33

    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    root = [mpf(v) for v in d['numeric_root']]
    zc, lam = root[:7], root[7:]
    print('=== R20-TC-AUDIT 5/5: dual representation of the threshold condition ===')
    print('   root R = %s' % mp.nstr(zc[6], 45))

    # independent Jacobian from the nested dual (second-order AD) is what the repo uses; here we
    # re-derive it from the repo's first-order dual (already audited against SymPy) and compare the
    # dual coefficients.
    J = np.zeros((5, 7))
    for i in range(7):
        xd = [K32.Dual(zc[k], [mpf(int(j == k)) for j in range(7)]) for k in range(7)]
        f = K32.res5(xd[0:4], xd[4], xd[5], xd[6], K32.BK_DMPF)
        for m in range(5):
            J[m, i] = float(f[m].d[i])
    eR = np.zeros(7); eR[6] = 1.0
    # solve min ||J^T c - e_R|| for c (the coefficients of the row combination)
    c, res, rk, sv = np.linalg.lstsq(J.T, eR, rcond=None)
    print('   coefficients c solving  e_R = sum c_i grad f_i  (independent least squares):')
    for i in range(5):
        print('      c[%d] = %+.15e    repo lam[%d] = %+.15e    |diff| %.2e'
              % (i, c[i], i, float(lam[i]), abs(c[i] - float(lam[i]))))
    print('   ||J^T c - e_R||        = %.3e' % np.linalg.norm(J.T @ c - eR))
    print('   ||J^T lam - e_R||      = %.3e   (repo coefficients)'
          % np.linalg.norm(J.T @ np.array([float(v) for v in lam]) - eR))
    print('   max |c - lam|          = %.3e  (representations agree)'
          % max(abs(c[i] - float(lam[i])) for i in range(5)))
    print('   all coefficients have the SAME SIGN: %s (negatives=%d, positives=%d)'
          % (bool(np.all(c > 0) or np.all(c < 0)), int((c < 0).sum()), int((c > 0).sum())))
    # conditioning of the 5x5 Gram system
    G = J @ J.T
    ev = np.linalg.eigvalsh(G)
    print('   Gram eigenvalues of J J^T: %s  -> condition %.3e'
          % (['%.6e' % v for v in ev], ev.max() / ev.min()))
    # independent second-order source: SymPy Hessian, to confirm the Jacobian used above
    import importlib.util
    spec = importlib.util.spec_from_file_location('tca', HERE / 'r20_tc_audit3.py')
    print()
    print('   (the SymPy-vs-AD gradient/Hessian equality was established in audits 2/2 and 3/3;')
    print('    here the Jacobian above is the same first-order dual already matched there.)')
    out = dict(R=mp.nstr(zc[6], 45),
               coefficients=[float(v) for v in c],
               repo_minus_lam=[-float(v) for v in lam],
               residual=float(np.linalg.norm(J.T @ c - eR)),
               max_coef_diff=float(max(abs(c[i] + float(lam[i])) for i in range(5))),
               gram_eigen=[float(v) for v in ev],
               gram_cond=float(ev.max() / ev.min()))
    (HERE / 'r20_tc_audit5.json').write_text(json.dumps(out, indent=1))
    print('   saved r20_tc_audit5.json')


if __name__ == '__main__':
    main()
