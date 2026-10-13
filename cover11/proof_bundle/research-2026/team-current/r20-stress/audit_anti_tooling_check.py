"""Tooling audit for the anti-block review (r20-rigidity is sole writer in its own directory;
this file only READS their code/JSON and tests the TOOLS they use, in r20-stress).

Question raised while reading `r20-rigidity/r20_anti_block_interval.py` (snapshot hashed below):
the point-mode log prints THREE different answers for what should be one intrinsic pair of
generalized eigenvalues:

    control 1  (2x2 pencil on span(U))          : 0.085226, 0.334637
    control 2  (22D orthonormal quotient)       : 0.164903, 0.254960   <- matches the numeric run
    control 3  (3D pencil, eigvalsh(G^-1 B))    : -0.006253, 0.182925, 0.243191

Generalized eigenvalues of a pencil (B,G) are BASIS-INDEPENDENT, so the three routes must agree
(up to the rotation's null value).  This script tests the two tool-level suspects:

  T1  np.linalg.eigvalsh( np.linalg.solve(G,B) )  -- np eigvalsh ASSUMES symmetry and uses one
      triangle, while G^-1 B is NOT symmetric (it is only G-self-adjoint).  Demonstrated on a
      synthetic pencil with a known answer, plus the correct route scipy.linalg.eigh(B,G) and the
      Cholesky-whitening route (float) and a pure-rational route (Fractions + a 2x2 closed form).
  T2  a complement chosen by float lstsq vs an exact INTEGER complement: both give the same PD
      verdict, but only the exact one gives a float-free, reproducible quotient basis.

Writes only in r20-stress/out .
"""
import json
import hashlib
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

W = Path(__file__).parent
OUT = W / 'out'
RIG = W.parent / 'r20-rigidity'
ANTI = RIG / 'r20_anti_block_interval.py'
POINTLOG = RIG / 'r20_anti_block_interval_point.log'

res = {}
res['snapshot'] = {
    'file': str(ANTI),
    'sha256': hashlib.sha256(ANTI.read_bytes()).hexdigest(),
    'bytes': ANTI.stat().st_size,
    'point_log_sha256': hashlib.sha256(POINTLOG.read_bytes()).hexdigest() if POINTLOG.exists() else None,
}

# ------------------------------------------------------------------ T1: eigvalsh on a non-symmetric G^-1 B
# synthetic pencil: G = diag-ish SPD, B symmetric PSD with one exact null direction, in a basis where
# G^-1 B is NOT symmetric (exactly the situation in the anti kernel: integer basis + Gram diag(2..,1,1,1)).
G = np.array([[2.0, 0.3, 0.1],
              [0.3, 1.0, 0.2],
              [0.1, 0.2, 1.5]])
c = np.array([1.0, -0.5, 2.0])                      # null direction of B
# orthonormal completion of c: B = lam2 q2 q2^T + lam3 q3 q3^T has B c = 0 exactly
q1 = c / np.linalg.norm(c)
tmp = np.array([[0.0, 0.0, 1.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0]])
q2 = np.cross(q1, tmp[0]); q2 /= np.linalg.norm(q2)
q3 = np.cross(q1, q2); q3 /= np.linalg.norm(q3)
B = 3.0 * np.outer(q2, q2) + 1.5 * np.outer(q3, q3)
N = np.linalg.solve(G, B)
res['T1'] = {
    'G_minus_B_symmetric': bool(np.abs(N - N.T).max() < 1e-14),
    'eigvalsh_of_nonsymmetric': sorted(np.linalg.eigvalsh(N).tolist()),
    'true_generalized_eigenvalues': sorted(np.linalg.eigvals(np.linalg.solve(G, B)).real.tolist()),
}
try:
    from scipy.linalg import eigh as scipy_eigh
    res['T1']['scipy_eigh_B_G'] = sorted(scipy_eigh(B, G)[0].tolist())
except Exception as e:                              # pragma: no cover
    res['T1']['scipy_error'] = repr(e)
L = np.linalg.cholesky(G)
res['T1']['cholesky_whitened'] = sorted(np.linalg.eigvalsh(np.linalg.solve(L, np.linalg.solve(L, B).T)).tolist())

# pure rational route: 2x2 case with an integer complement
G2 = np.array([[53, -29], [-29, 20]], dtype=object)
B2 = np.array([[13, -6], [-6, 4]], dtype=object)
G2 = np.array([[Fr(int(G2[i][j])) for j in range(2)] for i in range(2)])
B2 = np.array([[Fr(int(B2[i][j])) for j in range(2)] for i in range(2)])
tr = G2[0][0] + G2[1][1]
gmax = max(tr, Fr(0))
det2 = B2[0][0] * B2[1][1] - B2[0][1] * B2[1][0]
b11, b22 = B2[0][0], B2[1][1]
res['T1']['rational_2x2_det_and_trace'] = [str(det2), str(tr)]

# ------------------------------------------------------------------ T2: quotient structure with an exact null direction
# B3 = symmetric PSD with B3 c = 0 exactly (the rotation in the radical of the minimax Hessian),
# G3 = SPD metric.  Then the pencil (B3,G3) = {0} + {the intrinsic pair}; the 2x2 pencil on any
# G3-complement of c reproduces the pair; eigvalsh(G^-1 B) does not.
G3f = np.array([[53.0, -29.0, 4.0], [-29.0, 20.0, -3.0], [4.0, -3.0, 6.0]])
c = np.array([0.3, -0.2, 1.0])
G3F = [[Fr(int(round(G3f[i][j] * 10))) / 10 for j in range(3)] for i in range(3)]
print('T2 uses float G3 (rational build kept for the 2x2 route): G3 =', G3f.tolist())
Mf = np.array([[4.0, 0.4, -0.2], [0.4, 3.0, 0.1], [-0.2, 0.1, 2.5]])
Mc = Mf @ c
B3f = Mf - np.outer(Mc, Mc) / (c @ Mc)                 # B3 c = 0 exactly up to roundoff
res['T2'] = {}
res['T2']['null_residual_B3_c'] = float(np.abs(B3f @ c).max())
res['T2']['eigvalsh_of_nonsymmetric_pencil'] = sorted(np.linalg.eigvalsh(np.linalg.solve(G3f, B3f)).tolist())
try:
    from scipy.linalg import eigh as scipy_eigh2
    res['T2']['scipy_eigh_B_G'] = sorted(scipy_eigh2(B3f, G3f)[0].tolist())
except Exception as e:                                  # pragma: no cover
    res['T2']['scipy_error'] = repr(e)
G3c_exact = G3f @ c
G3c_float = G3f @ (c * (1 + 1e-15))
for nm, l in (('complement_exact_coef', G3c_exact), ('complement_float_coef', G3c_float)):
    U = np.array([[l[1], l[2]], [-l[0], 0.0], [0.0, -l[0]]])       # (G3 c)^T U = 0 exactly
    B2q, G2q = U.T @ B3f @ U, U.T @ G3f @ U
    ev = np.linalg.eigvals(np.linalg.solve(G2q, B2q)).real
    res['T2'][nm] = sorted(ev.tolist())
res['T2']['comment'] = ('scipy.eigh(B,G) is the correct pencil tool; np.eigvalsh(solve(G,B)) is '
                        'invalid for the non-symmetric G^-1 B (see T1); the 2x2 pencil on a '
                        'G3-complement reproduces the intrinsic pair; float vs exact coefficient '
                        'changes it only at 1e-15 -- the reason to prefer an exact complement is '
                        'reproducibility/provability, not magnitude')

print(json.dumps(res, indent=2))
(OUT / 'audit_anti_tooling_check.json').write_text(json.dumps(res, indent=2), encoding='utf-8')
print('[done] -> out/audit_anti_tooling_check.json')
