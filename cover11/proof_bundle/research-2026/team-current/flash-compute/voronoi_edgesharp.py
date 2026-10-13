# -*- coding: utf-8 -*-
"""voronoi_edgesharp.py -- edge-level (congruence) envelope maximised over the topology
parameters, and compared with pi.  Numeric screening only, NOT a certificate.

Structure used (all verified numerically on the saved object in voronoi_edges.py):
  * each interior Voronoi edge carries the SAME apex angle tau_e at both endpoints
    (congruence, |tau_a - tau_b| < 1e-15);
  * ring cell budget : 2pi = alpha_i + sum_{e in rr} tau_e + sum_{e in hr} tau_e
  * hub cell budget  : 2pi = sum_{e in hr} tau_e + d tau_hh   (per hub)
  * hence  S_hr = sum_{hr} tau_e = 4pi - 2 d tau_hh,
           S_rr = sum_{rr} tau_e = 7pi - A/2 + d tau_hh,  A = sum alpha_i.
  * area bound per component:
      caps + arc triangles : sum_i Seg(beta_i) + (1/2) r^2 sum_i sin alpha_i,
          with beta_i <= f(alpha_i) = 2 asin(r sin(alpha_i/2)) and sum beta_i >= 2pi
      ring-ring edges  : r^2 sum_{rr} sin tau_e   <= r^2 E_rr sin(S_rr/E_rr)   (Jensen)
      hub-ring edges   : r^2 sum_{hr} sin tau_e   <= r^2 min( E_hr sin(S_hr/E_hr),
                                                              k1 sin(2pi/k1)+k2 sin(2pi/k2) - d sin tau_hh )
      hub-hub edge     : r^2 sin tau_hh
  * combinatorics: E = E_rr + E_hr + d <= 21, E_rr >= 9, K = k1+k2 = E_hr + 2d,
      k_j >= 3, sum q = 2 E_rr + E_hr = 2E - K.
"""
import math

PI = math.pi


def f_r(r, a):
    return 2 * math.asin(min(1.0, r * math.sin(a / 2)))


def Seg(b):
    return (b - math.sin(b)) / 2


def caps_max(r, A):
    """max sum_i Seg(beta_i) with sum beta_i <= 9 f(A/9), each beta_i <= 2 asin(r),
       Seg convex  => concentrate the total angle."""
    tot = 9 * f_r(r, A / 9.0)
    bmax = 2 * math.asin(min(1.0, r))
    n_full = int(tot / bmax)
    rem = tot - n_full * bmax
    return n_full * Seg(bmax) + Seg(rem), tot


def E_sharp(r, verbose=False):
    """E_rr and E_hr are pushed to the budget boundary: E = 21 (more edges only helps,
       since E sin(S/E) is increasing in E for S/E in (0,pi)), so
         E_hr = K - 2d ,  E_rr = 21 - K + d ,   K = k1+k2 <= 12 + d."""
    best = None
    A_grid = [0.05 * i for i in range(1, int(9 * PI / 0.05) + 1)]
    tau_grid = [0.02 * i for i in range(0, int(PI / 0.02) + 1)]
    for d in (0, 1):
        for K in range(6, 12 + d + 1):
            E_hr = K - 2 * d
            E_rr = 21 - K + d
            if E_hr < 0 or E_rr < 9:
                continue
            hubmax = K * math.sin(4 * PI / K) if K > 0 else 0.0
            for A in A_grid:
                a_i = A / 9.0
                if a_i > PI:
                    continue
                # feasibility: the nine arcs must cover the circle, sum beta_i >= 2 pi, and
                # sum beta_i <= 9 f(A/9) (concavity of f), hence 9 f(A/9) >= 2 pi.
                if 9 * f_r(r, a_i) < 2 * PI - 1e-12:
                    continue
                c, _ = caps_max(r, A)
                base = c + 0.5 * r * r * 9 * math.sin(a_i)
                for tau in tau_grid:
                    S_hr = 4 * PI - 2 * d * tau
                    S_rr = 7 * PI - A / 2 + d * tau
                    if S_hr < 0 or S_rr < 0:
                        continue
                    if S_hr > E_hr * PI + 1e-9 or S_rr > E_rr * PI + 1e-9:
                        continue
                    rr = E_rr * math.sin(S_rr / E_rr)
                    hr1 = E_hr * math.sin(S_hr / E_hr) if E_hr > 0 else 0.0
                    hr2 = hubmax - d * math.sin(tau)
                    hr = min(hr1, hr2) if E_hr > 0 else 0.0
                    val = base + r * r * (rr + hr + d * math.sin(tau))
                    if best is None or val > best[0]:
                        best = (val, d, E_rr, E_hr, A, tau, K)
    if verbose and best:
        print("   E_sharp(%.4f) = %.6f  (pi=%.6f, slack %+.6f)  d=%d K=%d E_rr=%d E_hr=%d A=%.3f tau_hh=%.3f"
              % (r, best[0], PI, best[0] - PI, best[1], best[6], best[2], best[3], best[4], best[5]))
    return best


if __name__ == "__main__":
    print("edge-level (congruence) envelope maximised over topology + angle parameters")
    for r in (0.3800, 0.3790, 0.3760, 0.3720, 0.3710, 0.3709, 0.3700, 0.3680, 0.3660, 0.3640):
        E_sharp(r, verbose=True)
