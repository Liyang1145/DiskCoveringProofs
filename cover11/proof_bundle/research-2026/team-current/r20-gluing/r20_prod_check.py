"""R20-PROD-CHECK: line-by-line audit of my family against the authoritative producer.

The producer `lead/q0_lower375_dual.py` fixes (lead-confirmed):
  line 15: const[eta] = 0
  line 37: "# no ear capacity constraint in q0"   (the kappa family is NOT assembled)
  line 44: bounds[eta] = (0, 0)  -> z[72] is pinned 0
The certifier `lead/certify_q0_lower375.py` asserts z[eta] == 0 and z[kap:] >= 0.

Consequence: ETA is identically 0 in this family, so NO factor may carry an ETA coefficient.
The earlier probe (`r20_factor_probe.Model.ring_coefs`) DOES add `+z[eta]` for rings i >= 3; that
is a different family and must not be used to justify the producer family. This script checks that
`r20_producer_family.value_and_row` adds no ETA term, and audits every column index against the
producer's construction.

Also checks the assembled identity at the candidate:
    const(z) + sum_k (v_k(pi*) + M_k(pi*).z)  ==  pi     for the saved z,
and that this is slack bookkeeping (the equalities the candidate satisfies) rather than a bound.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_prod_check.py
"""
import json, math, sys
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row


def main():
    C = load_candidate(R_CAND); p0 = C['p']
    print('=== R20-PROD-CHECK: index audit against lead/q0_lower375_dual.py ===')
    # ---- ETA must never appear
    ETA_hits = []
    for k in range(29):
        v, M = value_and_row(k, p0, C)
        if abs(M[ETA]) > 0:
            ETA_hits.append((k, float(M[ETA])))
    print('  ETA column (72) coefficients across all 29 factors: %d nonzero' % len(ETA_hits))
    print('    producer line 15/44 force z[eta] = 0, so no ETA coefficient may appear: %s'
          % ('PASS' if not ETA_hits else 'FAIL %s' % ETA_hits))
    # ---- kappa: the producer assembles z[kap] * theta (line 26-30) but has no ear constraint,
    #      while its certifier asserts z[kap:] >= 0. So the kappa columns DO appear in M.
    kap_hits = sum(1 for k in range(29) for j in range(KAP, KAP + 21) if abs(value_and_row(k, p0, C)[1][j]) > 0)
    print('  kappa columns appearing in M: %d entries (producer has no ear constraint; certifier'
          ' pins z[kap:] >= 0)' % kap_hits)
    # ---- LAM: the ring factor carries w
    lam_hits = sum(1 for k in range(29) if k >= 20 and abs(value_and_row(k, p0, C)[1][LAM]) > 0)
    print('  LAM coefficients in ring factors: %d of 9' % lam_hits)
    # ---- assembled identity at the candidate
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    print()
    print('  z_c825: z[eta] = %.1f (must be 0) ; z[kap] min = %.3e (certifier asserts >= 0)'
          % (zc[ETA], zc[KAP:KAP + 21].min()))
    const = (PI * (zc[:9].sum() + 2 * zc[9:11].sum() + zc[KAP:LAM].sum() - 2 * zc[LAM]
                   - 2 * zc[ETA]) + 2 * zc[ETA] * math.asin(2 * R_CAND) - PI * zc[CL:].sum())
    tot = const
    for k in range(29):
        v, M = value_and_row(k, p0, C)
        tot += v + M @ zc
    print('  const(z_c825) = %.12f' % const)
    print('  sum_k (v_k + M_k . z_c825) = %.12f'
          % (tot - const))
    print('  V(z_c825; pi*) = %.12f   (pi = %.12f, excess %+.3e)' % (tot, PI, tot - PI))
    print('  -> this is the assembled identity at the candidate (all dualized equalities hold'
          ' there); it is a value match, NOT a proof that V is a valid bound.')
    # ---- scope check: V(same z) at a nearby but infeasible tuple
    print()
    print('  --- is V a BOUND?  test the constraint families at a random tuple ---')
    rng = np.random.default_rng(4)
    X = p0.copy()
    for t in range(11):
        X[3 * t] = rng.uniform(0.5, 2.5); X[3 * t + 1] = rng.uniform(0.5, 2.5)
        X[3 * t + 2] = rng.uniform(0.3, 1.0)
    for i in range(9):
        X[33 + i] = rng.uniform(0.3, 1.4); X[42 + i] = rng.uniform(0.3, 1.0)
    for i in range(9):
        X[51 + 3 * i] = rng.uniform(0.5, 2.5)
        X[51 + 3 * i + 1] = rng.uniform(0.2, 1.0); X[51 + 3 * i + 2] = rng.uniform(0.2, 1.0)
    vt = sum(value_and_row(k, X, C)[0] + value_and_row(k, X, C)[1] @ zc for k in range(29))
    print('  V(z_c825; X) for a random X = %.6f   (V(pi*) = %.6f)' % (vt, tot))
    print('  difference (must be <= 0 for pi* to be a simultaneous maximum): %+.6f'
          % (vt - tot))


if __name__ == '__main__':
    main()
