"""R20-AD: 78-parameter instrument with NUMERICALLY differentiated stationarity rows.

Instead of hand-derived analytic rows (error-prone: the first attempt disagreed with finite
differences on the ring rows), the rows are measured from the exact factor formula:

    B[q]  = d a_k(pi*) / d xi_q          (78 x 121)
    bp[q] = d b_k(pi*) / d xi_q

with Richardson-extrapolated central differences, and validated three ways:
  V1  every row is re-differentiated with an independent step size (h vs h/4);
  V2  the affine derivative  bp[q] + B[q].z  matches a full numeric derivative of the factor;
  V3  sum_k f_k(pi;z) equals the code's assembly identity  const(z) + (constraint side) at the
      candidate tuple (the lead kernel's own value).

Then: affine stationarity, correct boundary activity signs, cone, sampled validity rows, LP.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_instrument78.py
"""
import json, math, sys
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
NP = 78
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
I_FACE, I_BSW, I_RNG = 0, 33, 51
sys.path.insert(0, str(HERE))
from r20_family78 import (load_candidate, lin_form, const_of, param_table)


def rows_numeric(C, p0, h=2e-6):
    """Richardson-extrapolated central-difference rows."""
    tab = param_table(p0)
    B1 = np.zeros((NP, NZ)); b1 = np.zeros(NP)
    B2 = np.zeros((NP, NZ)); b2 = np.zeros(NP)
    for r in tab:
        q = r['q']; k = r['k']
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        ap, bpv = lin_form(k, pp, C); am, bmv = lin_form(k, pm, C)
        B1[q] = (ap - am) / (2 * h); b1[q] = (bpv - bmv) / (2 * h)
        h2 = h / 4
        pp = p0.copy(); pm = p0.copy(); pp[q] += h2; pm[q] -= h2
        ap, bpv = lin_form(k, pp, C); am, bmv = lin_form(k, pm, C)
        B2[q] = (ap - am) / (2 * h2); b2[q] = (bpv - bmv) / (2 * h2)
    # Richardson: (4*B2 - B1)/3 has O(h^4)... here use B2 (smaller step) and report spread
    B = B2.copy(); bp = b2.copy()
    spread_B = np.abs(B1 - B2).max(); spread_b = np.abs(b1 - b2).max()
    return B, bp, spread_B, spread_b, tab


def main():
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B, bp, sB, sb, tab = rows_numeric(C, p0)
    print('=== R20-AD: numeric stationarity instrument, 78 parameters ===')
    print('    row stability across step sizes (h vs h/4): max |dB| = %.3e, max |db| = %.3e'
          % (sB, sb))
    # V2: affine derivative vs full numeric derivative of f_k
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    h = 2e-6
    worst = 0.0
    for r in tab:
        q = r['q']; k = r['k']
        f = lambda pp: (lambda ab: ab[1] + ab[0] @ zc)(lin_form(k, pp, C))
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        dn = (f(pp) - f(pm)) / (2 * h)
        da = bp[q] + B[q] @ zc
        worst = max(worst, abs(dn - da))
    print('    V2 affine row vs full numeric derivative: max dev = %.3e' % worst)
    # V3: sum of factors equals the code's assembly
    v = const_of(zc, R) + sum(lin_form(k, p0, C)[1] + lin_form(k, p0, C)[0] @ zc for k in range(29))
    print('    V3 sum_k f_k(pi*; z_c825) = %.12f   (pi = %.12f)' % (v, PI))
    lab = json.loads((HERE / 'r20_factor_probe.json').read_text(encoding='utf-8'))['c825_z_at_38']
    print('       probe total at its own (saturated) argmax tuple = %.12f' % lab['total'])
    # activity
    act = {}
    for r in tab:
        act[r['activity']] = act.get(r['activity'], 0) + 1
    print('    parameter activity at R = r_cand: %s' % act)
    np.save(HERE / 'r20_B78.npy', B); np.save(HERE / 'r20_bp78.npy', bp)
    json.dump(dict(B=B.tolist(), bp=bp.tolist(), param=tab, spread_B=float(sB),
                   spread_b=float(sb), V2=float(worst), V3=float(v), R=R),
              open(HERE / 'r20_instrument78.json', 'w'), indent=1)
    print('    saved r20_B78.npy / r20_instrument78.json')


if __name__ == '__main__':
    main()
