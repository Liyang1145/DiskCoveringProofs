"""n12 -- eccentric-direction weighted capacity LP for k=11 at r = U.

Two necessary conditions for a k=11 cover at radius r (hub disc B(h,r),
|h| = e; ring discs of norm t_i in [1-r, sqrt(1-r^2)]):

 (A) S^1 is covered by the ring arcs; arc i has half-width
       alpha(t) = arccos((1 + t^2 - r^2)/(2t))  (< asin r),
     hence  sum_i alpha_i >= pi.

 (B) REACH (per-ray interior condition).  Along the direction beta (measured
     from the backward ray, i.e. from the direction opposite to h) the hub
     covers [0, R(beta)] with
       R(beta) = -e cos(beta) + sqrt(r^2 - e^2 sin^2(beta)),
     and the ring must reach down to R(beta).  Ring disc i (norm t, centre
     direction gamma) satisfies this at beta iff, with d = dist(beta,gamma),
       t sin d <= r   and  ( R sin d > r  or  t <= f(R,d) ),
       f(R,d) = R cos d + sqrt(r^2 - R^2 sin^2 d).
     Write T_i for the set of beta where disc i works.  Then  U_i T_i = S^1
     and hence  sum_i |T_i| >= 2 pi.

Therefore for every lambda >= 0
     sum_i [ alpha_i + lambda |T_i| ]  >=  pi + 2 pi lambda,
     and the LHS is at most 11 * max_{gamma,t} [ alpha(t) + lambda |T(gamma,t)| ].
If for some lambda the right-hand side is smaller than the left-hand lower
bound, k=11 is impossible at radius r.

Run: py -3 lamlp.py [r]
"""
import json
import sys
import numpy as np

U = 0.361102963744508672616920293904


def alpha(t, r):
    c = (1.0 + t * t - r * r) / (2.0 * t)
    return np.arccos(np.clip(c, -1.0, 1.0))


def R_hub(beta, r, e):
    s = np.sin(beta)
    return -e * np.cos(beta) + np.sqrt(np.maximum(0.0, r * r - e * e * s * s))


def territory_measure(gamma, t, r, e, betas):
    """measure of {beta : disc (gamma,t) satisfies the REACH condition}."""
    R = R_hub(betas, r, e)
    d = np.abs((betas - gamma + np.pi) % (2.0 * np.pi) - np.pi)
    meets = t * np.sin(d) <= r
    f = R * np.cos(d) + np.sqrt(np.maximum(0.0, r * r - R * R * np.sin(d) ** 2))
    good = R * np.sin(d) <= r
    ok = meets & ((~good) | (t <= f))
    return ok


def lp_bound(r, e, n_gamma=96, n_t=40, n_beta=2880):
    betas = np.linspace(-np.pi, np.pi, n_beta, endpoint=False)
    lo, hi = 1.0 - r, np.sqrt(max(0.0, 1.0 - r * r))
    gammas = np.linspace(-np.pi, np.pi, n_gamma, endpoint=False)
    ts = np.linspace(lo, hi, n_t)
    A = alpha(ts, r)                              # (n_t,)
    meas = np.zeros((n_gamma, n_t))
    for ig, g in enumerate(gammas):
        for it, t in enumerate(ts):
            meas[ig, it] = np.count_nonzero(territory_measure(g, t, r, e, betas))
    meas *= (2.0 * np.pi / n_beta)
    best = []
    for lam in np.arange(0.0, 6.01, 0.05):
        obj = A[None, :] + lam * meas               # (n_gamma,n_t)
        mx = float(obj.max())
        lhs = 11.0 * mx
        rhs = np.pi + 2.0 * np.pi * lam
        best.append((float(lam), lhs, rhs, lhs - rhs))
    return best, A, meas


if __name__ == "__main__":
    r = float(sys.argv[1]) if len(sys.argv) > 1 else U
    out = {}
    print("r=%.15f" % r)
    for e in (0.0, 0.02, 0.05, 3.0 * r - 1.0):
        rows, A, meas = lp_bound(r, e)
        worst = min(rows, key=lambda z: z[3])
        print("  e=%.6f  best(lam,lhs,rhs,slack)=(%5.2f, %.4f, %.4f, %+.5f)  "
              "max|T|=%.4f" % (e, worst[0], worst[1], worst[2], worst[3],
                               meas.max()))
        out["e=%.5f" % e] = dict(best_lambda=worst[0], lhs=worst[1],
                                 rhs=worst[2], slack=worst[3])
    json.dump(out, open("lamlp_out.json", "w"), indent=1)
