"""cline2-coupled-factors f12: the ENDPOINT-COPY IDENTITY and its dual consequence.

THEOREM (sector endpoint symmetry).  Let P,Q be points of the unit circle and c a point
with |P-c| = |Q-c| (= r), with c on the inward side of the chord.  Then
      c . (P - Q) = 0        and hence      |P-c| = |Q-c|   identically,
i.e. the two endpoint radius copies of a ring sector are ALWAYS equal:
      u_k = v_k =: e_k      for every ring sector k.

Proof. |P-c|^2-|Q-c|^2 = |P|^2-|Q|^2-2c.(P-Q) = 0-2c.(P-Q), and the equal-distance
locus |P-c|=|Q-c| is exactly the perpendicular bisector of PQ, which contains c.
The saving defect 2[cos theta_{k-1}-cos theta_k] c^x + 2[sin theta_{k-1}-sin theta_k] c^y
is exactly -2 c.(P-Q).   []

In the dual this is a free EQUALITY row u_k - v_k = 0, so the sector factor's quadratic
block  -z_rr(2k) u^2 - z_rr(2k+1) v^2  may be replaced by  -(z_rr(2k)+z_rr(2k+1)) e^2
plus the free multiplier row.  Numerical check (f11 TEST 1): perturbing the switch angles
by up to 1e-2 changes |u-v| by < 1e-15 while the widths move by ~7e-3, i.e. the identity is
structural, not accidental.  Below we test whether opening this row improves the bound.
"""
import numpy as np, json, math, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import f4_feasible_dual as F
P = Path(__file__).parent
OUT = P / 'out'

# fix the f11 list-subtraction nit there
if __name__ == '__main__':
    import importlib
    d = np.load(OUT/'realized.npz', allow_pickle=True)
    PK = d['PK']; C = d['C']; slot = [int(s) for s in d['slot_site']]; Rc = float(d['Rc'])
    uu = np.array([np.linalg.norm(PK[(k-1) % 9]-C[s])/Rc for k, s in enumerate(slot)])
    vv = np.array([np.linalg.norm(PK[k]-C[s])/Rc for k, s in enumerate(slot)])
    print('saved object: max |u-v| =', np.abs(uu-vv).max())

    # --- 1D scan: does the u=v row help?  The row enters the ring factor as a shift of
    #     the u,v coefficients; we test the symmetric perturbation directly.
    pr = F.build(open_L=True)
    row = json.loads((P.parent/'lead'/'q0_closure_dual_0_4.json').read_text())
    z0 = np.concatenate([np.array(row['z']), np.zeros(21)])
    print(f'{"eps on L":>10s} {"bound":>16s} {"delta":>14s}')
    for eps in [0.0, 0.01, 0.05, 0.1, 0.2, 0.5]:
        z = z0.copy(); z[121:] = eps
        ub = float(pr['base'] @ z)
        for name, v, M in pr['factors']:
            ub += float(np.max(v + M @ z))
        print(f'{eps:10.3f} {ub:16.9f} {ub-3.175702557547944:14.3e}')
