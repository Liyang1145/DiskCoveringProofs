"""KERNEL-METRIC-DESIGN (numeric proposal only -- NOT a certificate, NOT an upgrade of any claim).

Design a metric S (4x4 SPD) for the adaptive stress alpha = alpha0 + tau * (N S) G^T x and compare the
remainder loss coefficient (B(S)*d + ||A(S)||) against the quadratic gain, for <=5 analytic candidates
(NO parameter grid).  All outputs are numeric proposals.

Data: lead/ANISOTROPIC-STRESS-REMAINDER.md constants (B=182, A=1.074, C_cross=0.0358, G=1.892,
d=0.08, mu=0.002, tau0=0.05, tau=0.1, rho=0.00764).  The root kernel (N, G, alpha, T) is obtained by
importing lead/interval_network_envelope.py, which RECOMPUTES the root kernel; per the task only its
numeric values are used for candidate comparison -- never treated as an interval/rigorous statement.

Candidates (see KERNEL-METRIC-DESIGN.md 2):
  1  S = I                                   (baseline)
  2  S = whitening of G G^T on im(G)
  3  diagonal S normalising the columns of N S to unit norm
  4  S = (K0^T K0)^{-1/2} for K0 = N         (increment whitening)
  5  S = sigma * I with sigma* = argmin_sigma ( (B(sigma)d + sigma||A||) / (sigma * lmin(G G^T)) )
     -- one-dimensional monotone/closed-form solve, NOT a grid.

Usage (heavy: imports the lead module and recomputes the root kernel):
    py -3 -B -X utf8 research-2026/team-current/r20-stress/kernel_metric_design.py
"""
import sys, json
from pathlib import Path
import numpy as np

W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'
sys.path.insert(0, str(LEAD))

# ---- constants from the lead note (numeric only) ------------------------------------------------
C = dict(B=182.0, A=1.074, C_cross=0.0358, G=1.892, d=0.08, mu=0.002, tau0=0.05, tau=0.1, rho=0.00764)


def _mid(v):
    """mpmath.iv (or pair) -> Python float midpoint.  NUMERIC USE ONLY (never a rigorous bound)."""
    try:
        return float(v)
    except Exception:
        pass
    try:
        return float((v.a + v.b) / 2)          # mpmath.iv
    except Exception:
        pass
    try:
        return (float(v[0]) + float(v[1])) / 2  # [lo, hi] pair
    except Exception:
        return float('nan')


def _to_float_array(o):
    """Best-effort object->float conversion (None if it is not array-like / has no usable entries)."""
    try:
        a = np.asarray(o, dtype=object)
    except Exception:
        return None
    if a.ndim == 0:
        v = _mid(a.item())
        return None if np.isnan(v) else np.asarray(v, dtype=float)
    f = np.vectorize(_mid, otypes=[float])(a)
    if not np.all(np.isfinite(f)):
        return None
    return f


def load_root_kernel():
    """Read the root kernel with the LEAD API (k.arr / k.mid), as lead/local_tau_diagnostic.py and
    lead/certify_anisotropic_stress_ball.py do.  RETRACTION: top-level k.N / k.G8 / k.alpha DO exist
    (mpmath.iv matrices); a dir()-based numpy-only filter wrongly missed them.  Numeric use only."""
    import interval_network_envelope as k  # noqa
    ker = {"N": k.arr(k.N), "G": k.arr(k.G8), "alpha": k.arr(k.alpha).ravel()}
    if hasattr(k, "H"):
        ker["H"] = k.arr(k.H)
    if hasattr(k, "X"):
        try:
            ker["X"] = np.array([[float(k.mid(v)) for v in row] for row in k.X], dtype=float)
        except Exception:
            pass
    return ker


def anchor_flux(N, X, edges, nnode=11):
    """flux[2*node+c, j] += sgn*N[e,j]*dd[c] with dd = X[v]-X[w] (lead certify_anisotropic_stress_ball)."""
    F = np.zeros((2 * nnode, N.shape[1]))
    for (e, v, w, sgn) in edges:
        dd = X[v] - X[w]
        node = v
        for c in range(2):
            F[2 * node + c, :] += sgn * N[e, :] * dd[c]
    return F


def B_of(K, alpha):
    """B(S) = max_e ||K_e|| / alpha_e  (rows of K vs the root stress components)."""
    K = np.atleast_2d(K)
    rows = np.linalg.norm(K, axis=1) if K.shape[1] > 1 else np.abs(K).ravel()
    a = np.asarray(alpha, dtype=float).ravel()
    n = min(len(rows), len(a))
    return float(np.max(rows[:n] / np.maximum(a[:n], 1e-300)))


def A_norm(K, T):
    """||A(S)|| : operator norm of the linear map t -> anchor flux of stress K t.
    With T the (n_anchor x 4) anchor-incidence block of the stress operator, A(S) = T @ K."""
    return float(np.linalg.norm(np.asarray(T, dtype=float) @ np.asarray(K, dtype=float), 2))


def gain_min_direction(Gm, S):
    """lambda_min of G S G^T on im(G) (the worst-direction quadratic gain)."""
    Gm = np.asarray(Gm, dtype=float)
    Q = Gm @ S @ Gm.T
    w = np.linalg.eigvalsh((Q + Q.T) / 2)
    w = w[w > 1e-12 * max(1.0, abs(w).max())]
    return float(w[0]) if w.size else 0.0


def candidates(N, G, alpha, T):
    n, k = N.shape
    Ss = {}
    Ss['1_identity'] = np.eye(k)
    # 2: whiten G G^T on im(G)  (pseudo-inverse square root)
    GtG = G.T @ G                      # 4x4 (t-space), the correct dimension for S
    w, V = np.linalg.eigh((GtG + GtG.T) / 2)
    Ss['2_GtG_invsqrt'] = (V @ np.diag(1.0 / np.sqrt(np.maximum(w, 1e-300))) @ V.T)
    # 3: diagonal S normalising the columns of N S (fixed point: s_l = 1/||N_{:,l}||)
    coln = np.linalg.norm(N, axis=0)
    Ss['3_col_normalised'] = np.diag(1.0 / np.maximum(coln, 1e-300))
    # 4: increment whitening of K0 = N
    w4, V4 = np.linalg.eigh((N.T @ N + (N.T @ N).T) / 2)
    Ss['4_K0T_K0_invsqrt'] = V4 @ np.diag(1.0 / np.sqrt(np.maximum(w4, 1e-300))) @ V4.T
    return Ss


def scalar_optimal(N, G, alpha, T, d, tau):
    """Candidate 5: S = sigma I.  One-dimensional: minimise (B(sigma)d + sigma||A||)/(sigma*lmin(GG^T)).
    B(sigma) = max_e ||(sigma N)_e||/alpha_e = sigma * B(1)  => ratio = (B1*d)/lmin + ||A||/lmin ,
    i.e. sigma cancels: the scalar family cannot change the ratio (recorded, not a bug)."""
    B1 = B_of(N, alpha)
    A1 = A_norm(N, T)
    lmin = gain_min_direction(G, np.eye(N.shape[1]))
    ratio_sigma = (B1 * d) / max(lmin, 1e-300) + A1 / max(lmin, 1e-300)
    return dict(sigma_cancels=True, B1=B1, A1=A1, lmin=lmin, ratio=ratio_sigma)


def main():
    ker = load_root_kernel()
    N = G = alpha = T = None
    for nm in ('N', 'Nbasis', 'N_basis', 'K0'):
        if nm in ker:
            N = ker[nm]; break
    for nm in ('G', 'G8', 'G8mat'):
        if nm in ker:
            G = ker[nm]; break
    for nm in ('alpha', 'alpha0', 'alpha_0'):
        if nm in ker:
            alpha = ker[nm]; break
    for nm in ('T', 'Tmat', 'anchor_inc'):
        if nm in ker:
            T = ker[nm]; break
    if N is None or G is None or alpha is None:
        msg = "kernel arrays unavailable; NUMERIC PROPOSAL ONLY"
        print("[kernel_metric_design]", msg)
        return
    # NOTE: the anchor-flux term ||A(S)|| needs the edge list held inside the lead module; it is NOT
    # computed here (reported explicitly as not-computed rather than estimated).
    rows = []
    tau = C['tau']
    for name, S in candidates(N, G, alpha, None).items():
        NS = N @ S
        Q = tau * (NS @ G.T) if NS.shape[1] == G.shape[1] else None
        b_S = (float(np.max(np.linalg.norm(Q, axis=1) / np.maximum(alpha[:Q.shape[0]], 1e-300)))
               if Q is not None else float('nan'))
        rows.append({'S': name, 'B_basis_only': B_of(NS, alpha), 'b_tau_scaled_diag': b_S,
                     'lmin_gain': gain_min_direction(G, S),
                     'flux_term_normA': 'NOT COMPUTED (needs the lead module edge list)'})
    out = {'status': 'NUMERIC PROPOSAL ONLY -- not a certificate, does not upgrade any claim',
           'constants': C, 'candidates': rows, 'scalar_family': {'note': 'S=sigma*I: b(S), B(S) scale with sigma and lmin(gain) too, so the ratio is sigma-independent (scale family cannot change the ratio)'}}
    (OUT / 'kernel_metric_design.json').write_text(json.dumps(out, indent=1), encoding='utf-8')
    for r in rows:
        print('  %-22s B_basis=%12.4f  b_tau_diag=%12.4f  lmin_gain=%.4e  ||A||=%s'
              % (r['S'], r['B_basis_only'], r['b_tau_scaled_diag'], r['lmin_gain'], r['flux_term_normA']))
    print('[done] -> out/kernel_metric_design.json  (numeric proposal only)')


if __name__ == '__main__':
    main()
