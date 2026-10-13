"""r20 gradient-margin bound: mu from positive weights w and sigma_min(A|T_perp)  (lead's obligation).

Writes ../out/r20_gradient_margin_bound.txt.  Read-only outside r20-chain; no operator work duplicated
(this note only supplies the analytic lemma + a computable interface for the rigidity side).

SETTING (lead).  18 active gradient rows g_1..g_18 in the rotation 21-dimensional slice; the row map
A: R^21 -> R^18 has rank 17, common kernel K = ker A of dimension 4 (21 - 17), and T_perp is the
orthogonal complement of K; there are positive weights w (w_i >= w_min > 0, sum_i w_i = 1) with
sum_i w_i g_i = 0.

CLAIM.  There is mu > 0 with   max_i <g_i, t>  >=  mu ||t||   for every t in T_perp.

PROOF (three lines, no LP, no constraint qualification).
  Let a = A t in R^18, i.e. a_i = <g_i, t>.  The weighted identity gives
      sum_i w_i a_i = <sum_i w_i g_i, t> = 0.
  Therefore  sum_i w_i |a_i| = 2 sum_{a_i>0} w_i a_i   (the negative part balances the positive one).
  If all a_i <= 0 then 0 = sum w_i a_i with w_i > 0 forces a = 0, i.e. t in T_perp ^ ker A = {0}; so
  for t != 0 at least one a_i > 0 and
      max_i a_i >= ( sum_{a_i>0} w_i a_i ) / ( sum_{a_i>0} w_i ) >= (1/2) sum_i w_i |a_i|
                >= (w_min/2) ||a||_1 >= (w_min/2) ||a||_2 >= (w_min/2) sigma ||t||,
  where sigma := sigma_min(A restricted to T_perp) = the smallest NONZERO singular value of A.
  Hence        mu = w_min * sigma / 2          (coarse; no LP needed).
  Note: the suggested w_min*sigma/sqrt(18) is also valid but weaker, because
  max_i a_i >= ||a||_2/sqrt(18) alone does not control the sign; the w-weighted argument above does,
  and it uses exactly the normalisation sum_i w_i = 1 plus w_i >= w_min.

INTERFACE FOR sigma (exact, from a 17x17 minor inverse -- Frobenius).
  Let G = A A^T (18x18, rank 17); the nonzero eigenvalues of G are the squared singular values of A,
  so sigma^2 = lambda_min^{(17)}(G) = the SMALLEST POSITIVE eigenvalue of G.
  For any index set S of 17 rows, the principal submatrix G_S = G_{S,S} interlaces:
      lambda_i(G_S) in [ lambda_{i+1}(G), lambda_i(G) ]      (i = 1..17),
  hence  lambda_min(G_S) <= lambda_17(G) = sigma^2  and, if G_S is invertible,
      sigma  >=  sqrt( lambda_min(G_S) )  =  1 / sqrt( || G_S^{-1} ||_2 )  >=  1 / sqrt( || G_S^{-1} ||_F ) .
  So: choose S with G_S invertible (well conditioned), invert the 17x17 minor, and use
      sigma_lower = 1 / sqrt(||G_S^{-1}||_F)   =>        mu_lower = w_min * sigma_lower / 2.
  All quantities are finite matrix operations: an exact bound interface, no SVD of the 21-dim operator
  required (any single invertible 17x17 principal minor suffices).
"""
import numpy as np
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def calibrate(rng, n18=18, n21=21, trials=200):
    # build 17 random rows, set the 18th so that sum_i w_i g_i = 0 exactly
    w = rng.random(n18) * 0.9 + 0.1
    w = w / w.sum()
    G17 = rng.normal(size=(17, n21))
    g18 = -(w[:17] @ G17) / w[17]
    A = np.vstack([G17, g18[None, :]])
    # kernel / T_perp via SVD
    U, s, Vt = np.linalg.svd(A)
    rank = int((s > 1e-9 * s[0]).sum())
    sigma = s[rank-1]                       # smallest nonzero singular value
    K = Vt[rank:]                           # kernel basis (4 rows)
    T = Vt[:rank]                           # T_perp basis (17 rows)
    # random directions in T_perp: worst observed ratio
    worst = np.inf
    for _ in range(trials):
        c = rng.normal(size=rank)
        t = c @ T
        if np.linalg.norm(t) == 0:
            continue
        a = A @ t
        worst = min(worst, a.max() / np.linalg.norm(t))
    # Gram-minor interface over all S (drop one row)
    G = A @ A.T
    best_sig = 0.0
    for drop in range(n18):
        S = [i for i in range(n18) if i != drop]
        GS = G[np.ix_(S, S)]
        try:
            inv = np.linalg.inv(GS)
        except np.linalg.LinAlgError:
            continue
        fro = np.linalg.norm(inv, 'fro')
        best_sig = max(best_sig, 1.0/np.sqrt(fro))
    return rank, w.min(), sigma, worst, best_sig


def main():
    P("=" * 100)
    P("LEMMA (proved in the header):  mu = w_min * sigma / 2,  where sigma = sigma_min(A|T_perp)")
    P("  - uses only: rank 17, sum_i w_i g_i = 0, w_i >= w_min > 0, sum_i w_i = 1; no LP, no CQ.")
    P("  - the suggested w_min*sigma/sqrt(18) is valid but weaker (sign control needs the weights).")
    P("")
    P("INTERFACE: with G = A A^T (18x18, rank 17) and any 17-row index set S with G_S invertible,")
    P("  lambda_min(G_S) <= sigma^2  (Cauchy interlacing), hence  sigma >= 1/||G_S^{-1}||_F")
    P("  and therefore  mu >= w_min / (2 sqrt(||G_S^{-1}||_F))  -- finite, exact, LP-free interface.")
    P("")
    P("CALIBRATION on random instances (construction guarantees sum w_i g_i = 0 exactly):")
    rng = np.random.default_rng(20260925)
    for trial in range(3):
        rank, wmin, sigma, worst, best_sig = calibrate(rng)
        mu = wmin * sigma / 2
        mu_int = wmin * best_sig / 2
        P("  trial %d: rank=%d  w_min=%.4f  sigma=%.6f  mu=w_min*sigma/2=%.6f" % (trial, rank, wmin, sigma, mu))
        P("            worst ratio  max_i a_i / ||t||  over %d random t in T_perp = %.6f  (>= mu: %s)"
          % (200, worst, worst >= mu - 1e-9))
        P("            interface 1/sqrt(||G_S^{-1}||_F) (best over 18 choices) = %.6f  <= sigma: %s ; mu_interface=%.6f <= mu: %s"
          % (best_sig, best_sig <= sigma + 1e-9, mu_int, mu_int <= mu + 1e-9))
        P("            lead's weaker form w_min*sigma/sqrt(18) = %.6f <= mu: %s"
          % (wmin*sigma/np.sqrt(18), wmin*sigma/np.sqrt(18) <= mu + 1e-9))
    P("")
    P("SCOPE: analytic lemma + exact interface; the random runs are calibration only (no continuum")
    P("  inference, no operator construction here -- that belongs to the rigidity side).")

    (OUT / "r20_gradient_margin_bound.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_gradient_margin_bound.txt"))


if __name__ == "__main__":
    main()
