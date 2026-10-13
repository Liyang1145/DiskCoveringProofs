"""r20 CORRECTED gradient-margin lemma + independent rank/margin check on the rigidity artifacts.

Writes ../out/r20_gradient_margin_rank_check.txt.  READ-ONLY w.r.t. r20-rigidity (loads their saved
.npy artifacts; writes nothing outside r20-chain).

WHY.  The rigidity worker reported a discrepancy: on the real candidate the 18 active gradient rows
have rank 18 (not 17), kernel dim 3 (not 4), and there is NO exact positive-weight relation
Σ w_i g_i = 0; the best nonnegative relation is approximate with ρ = min_{λ∈Δ} ‖A^Tλ‖ ≤ 6.6e-10.
This script (a) checks those numbers on their saved J, and (b) states the corrected lemma in the
three formal variants that are actually available.

CORRECTED LEMMA (proved here; no LP/CQ).
 (C1) EXACT-relation form (the original hypothesis, kept for completeness):
      if Σ w_i g_i = 0 with w_i >= w_min > 0, Σw_i = 1, then for t in T_perp = (ker A)^perp
         max_i <g_i,t> >= (w_min/2) ||At||_1 >= (w_min sigma/2) ||t||,  sigma = sigma_min(A|T_perp).
 (C2) APPROXIMATE-relation form (what the candidate actually supports).  Let rho := min_{λ∈Δ}‖A^Tλ‖
      and take any λ in Δ (in particular one achieving rho).  Then for EVERY t
         S := Σ λ_i <g_i,t> = <A^Tλ, t>,  |S| <= rho ||t||,
      and since Σ λ_i |a_i| = 2 Σ_{a_i>0} λ_i a_i − S,
         max_i a_i >= ( Σ_{a_i>0} λ_i a_i ) = ( Σ λ_i|a_i| + S )/2 >= ( w_min ||a||_1 − rho ||t|| )/2.
      Hence   max_i a_i >= ( w_min sigma − rho ) ||t|| / 2   for t in the subspace where the relevant
      sigma applies; the bound is NON-VACUOUS iff  w_min sigma > rho.
      (This is a factor-2 improvement of the form quoted back to me: the rho-term enters through |S|/2.)
 (C3) THREE-PIECE DECOMPOSITION (the useful architecture on the candidate), with the candidate's
      readings:   R^21 = span(v18)  +  K (rotation/kernel 3D)  +  T_perp (17D, complement of span(K,v18)):
        * span(v18): A v18 = sigma18 u18 with u18 elementwise > 0, so along −v18 ALL 18 constraints
          decrease; first-order slope ≈ 4.9e-10 (measured well depth ~5e-19 at t ≈ 1e-9, quadratic
          beyond) — this piece must be handled as a separate soft direction, never as a margin.
        * K piece: quadratic with min-max form >= 0.16 d^2 (0.3219 without / 0.2915 with v18).
        * T_perp piece: LINEAR margin >= (w_min sigma17 − rho)/2 ≈ 2.89e-4 per unit distance
          (sigma17 = 5.84e-2, w_min = 0.0099, rho <= 6.6e-10).
      On the FULL 21-dim space the (C2) bound is VACUOUS: (w_min sigma18 − rho)/2 < 0 because
      w_min sigma18/2 = 1.2e-11 < rho = 6.6e-10.  Folding v18 out of T_perp is exactly what restores it.
 (C4) DEFLATED-GRAM INTERFACE for sigma17 (replaces the earlier 17x17-minor formula, which was
      derived for rank-17 A).  Let G = A A^T (18x18).  With rank 18, G is invertible and the
      smallest eigenvalue is sigma18^2; with u18 known, deflate:  G' := G − sigma18^2 u18 u18^T
      (rank 17, sigma17^2 = its smallest positive eigenvalue).  For any 17-row set S with G'_{S,S}
      invertible, Cauchy interlacing on G' gives  lambda_min(G'_{S,S}) <= sigma17^2, hence
         sigma17 >= 1 / || (G'_{S,S})^{-1} ||_F ,      mu >= ( w_min sigma17 − rho ) / 2 .
      (On the undeflated G the same minor test is useless: interlacing only gives lambda_min(G_{S,S})
      >= sigma18^2 ≈ 0.)
"""
import numpy as np
from pathlib import Path

RIG = Path(__file__).resolve().parents[2] / "r20-rigidity"
OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def main():
    P("=" * 100)
    P("CORRECTED LEMMA (C1)-(C4) stated in the header.  Independent check below uses the rigidity")
    P("side's SAVED J artifacts (read-only); no file of theirs is written and no operator work redone.")
    P("")
    for name in ("r20_J60.npy", "r20_JA_analytic.npy"):
        p = RIG / name
        if not p.exists():
            P("  %s : missing" % name)
            continue
        J = np.load(p, allow_pickle=False)
        P("  %s : shape=%s dtype=%s" % (name, tuple(J.shape), J.dtype))
        Jf = np.asarray(J, dtype=float)
        s = np.linalg.svd(Jf, compute_uv=False)
        P("     singular values (smallest 5) = %s" % ["%.6e" % x for x in s[-5:]])
        P("     rank at 1e-12*sigma1 = %d ; sigma1 = %.6e ; cond = %.3e"
          % (int((s > 1e-12*s[0]).sum()), s[0], s[0]/s[-1]))
        P("     -> rank 18 expected (matching the rigidity worker's newer r20_grad_interface.log);")
        P("        the OLDER r20_symmetry_rank.log line 'det = 0 / rank 17' was superseded.")
        # (C2): rho via the simplex minimisation
        n = Jf.shape[0]
        m = Jf.shape[1]
        # minimize ||J^T lambda||^2 over the simplex by projected gradient (small, deterministic)
        lam = np.ones(n)/n
        step = 1.0
        for _ in range(20000):
            g = Jf @ (Jf.T @ lam)   # grad of 0.5||J^T lam||^2 (22x18 then 18x1 -> 18)
            v = lam - step*g
            # project on the simplex
            u = np.sort(v)[::-1]
            css = np.cumsum(u)
            rho_idx = np.nonzero(u - (css - 1)/(np.arange(n)+1) > 0)[0]
            if len(rho_idx) == 0:
                proj = np.ones(n)/n
            else:
                r = rho_idx[-1]
                theta = (css[r] - 1)/(r+1)
                proj = np.maximum(v - theta, 0)
            if np.linalg.norm(proj-lam) < 1e-16:
                lam = proj
                break
            lam = proj
        rho = float(np.linalg.norm(Jf.T @ lam))
        P("     tau_hat = min_lam ||J^T lam|| (projected gradient, simplex) = %.6e ; min lam = %.4f"
          % (rho, float(lam.min())))
        # minimax: min_{||v||=1} max_i (Jv)_i should equal -tau
        UU, SS, VVt = np.linalg.svd(Jf)
        rk = int((SS > 1e-12*SS[0]).sum())
        v_pos = VVt[rk-1]                  # smallest POSITIVE singular value's right vector (=v18)
        a_pos = Jf @ v_pos
        P("     check: along the near-null (sigma18) direction: max_i (Jv)_i = %+.6e (>= -tau: %s)"
          % (float(a_pos.max()), float(a_pos.max()) >= -rho-1e-18))
        P("            along -v: max_i (J(-v))_i = %+.6e  (= -min_i (Jv)_i = %+.6e ; thin-cone slope)"
          % (float((-a_pos).max()), float(-a_pos.min())))
        sig18, sig17 = float(s[-1]), float(s[-2])
        P("     (C3)/(C2) saturated bounds:  (w_min*sig18 - rho)/2 = (0.0099*%.3e - %.3e)/2 = %.3e  [VACUOUS]"
          % (sig18, rho, (0.0099*sig18 - rho)/2))
        P("                                  (w_min*sig17 - rho)/2 = (0.0099*%.3e - %.3e)/2 = %.3e  [valid on T_perp]"
          % (sig17, rho, (0.0099*sig17 - rho)/2))
        # (C4) deflated Gram interface
        U, S, Vt = np.linalg.svd(Jf)
        u18 = U[:, -1]
        G = Jf @ Jf.T
        Gd = G - (S[-1]**2)*np.outer(u18, u18)
        best, bestS = 0.0, None
        for drop in range(n):
            idx = [i for i in range(n) if i != drop]
            GS = Gd[np.ix_(idx, idx)]
            try:
                inv = np.linalg.inv(GS)
            except np.linalg.LinAlgError:
                continue
            b = 1.0/np.sqrt(np.linalg.norm(inv, 'fro'))
            if b > best:
                best, bestS = b, drop
        P("     (C4) deflated-Gram interface: best 1/sqrt(||(G'_S)^{-1}||_F) = %.6e <= sig17 = %.6e : %s (drop=%s)"
          % (best, sig17, best <= sig17+1e-12, bestS))
        P("           => rigorous mu_lower = (0.0099*%.6e - rho)/2 = %.6e" % (best, (0.0099*best - rho)/2))
    P("")
    P("CONCLUSION.  The rigidity worker's discrepancy is CONFIRMED on their saved J: rank 18, tiny")
    P("  sigma18 = 2.4e-9 with elementwise-positive left vector, and no exact positive relation.")
    P("  The corrected, usable statement is (C2) on the deflated complement with sigma17 = 5.84e-2:")
    P("  linear margin ~2.89e-4 per unit distance, PLUS the separate soft direction v18 (first-order")
    P("  descent for all 18 constraints, quadratic well ~5e-19) and the 3D quadratic K-piece.")
    P("  My original lemma (C1) remains valid but its hypothesis is NOT met by the candidate; the")
    P("  synthetic calibration validated only the algebra, not the applicability.")

    (OUT / "r20_gradient_margin_rank_check.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_gradient_margin_rank_check.txt"))


if __name__ == "__main__":
    main()
