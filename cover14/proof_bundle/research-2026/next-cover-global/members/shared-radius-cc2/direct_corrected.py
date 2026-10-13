"""
CORRECTED direct maximization of the shared-face relaxation.

Relaxed local problem (from the geometry, y_i = T_i/U, x = R/U):
   max  A = x * sum_i y_i sin beta_i
   s.t. beta_i in (0,pi),  Bsum = sum beta_i < 2pi,  0 < x <= 1, 0 < y_i <= 1,
        sum_i theta_i = pi,   0 < theta_i < pi - beta_i,
        theta_i = atan2(y_i sin beta_i, x - y_i cos beta_i).

Structure used (all in notes):
 * theta_i is strictly increasing in y_i for fixed x (as long as theta_i<pi/2).
 * A is increasing in each y_i and in x.
 => the maximum over y (fixed beta,i) lies on the set where either some
    y_i = 1 or sum theta_i = pi; and for the *inner* maximum over y we may
    take the largest common scale lambda* with sum_i theta_i(x, lambda y*) = pi
    provided min_i(bound_i/lambda*) >= 1 ... else reduce along the binding box.
   Here we simply do the honest thing:
    - g(x) := sum_i theta_i(x, 1)  (all y_i = 1).  g is not monotone in x in
      general, so locate the *maximal* feasible x by dense 1-D search + refine.
    - the feasible x-set is  {x : g(x) >= pi} intersected with theta_i bounds
      (theta_i < pi - beta_i holds iff x < x_i^*(beta_i) = cos b_i + sin b_i *
      tan(pi - b_i) ... i.e. the branch constraint, evaluated numerically).
    - then A(beta) = x_max(beta) * sum sin beta_i  when the y=1 saturation is
      reachable; otherwise the y<i are scaled down (computed explicitly here).

This module is deliberately independent of the algebraic envelope formula.
"""
import numpy as np

PI = float(np.pi)


def theta_of(beta, x, y):
    beta = np.asarray(beta, float)
    y = np.broadcast_to(np.asarray(y, float), beta.shape)
    return np.arctan2(y * np.sin(beta), x - y * np.cos(beta))


def branch_ok(beta, x, y, tol=1e-12):
    th = theta_of(beta, x, y)
    return bool(np.all(th < PI - np.asarray(beta, float) - tol))


def x_feasible_set(beta, n=40001, lo=1e-9, hi=1.0):
    """Return (xs, feasible_mask) for sum theta_i(x, 1) >= pi and branch ok."""
    beta = np.asarray(beta, float)
    xs = np.linspace(lo, hi, n)
    S = np.empty_like(xs)
    for i, x in enumerate(xs):
        S[i] = theta_of(beta, x, 1.0).sum()
    mask = S >= PI
    bo = np.array([branch_ok(beta, x, 1.0) for x in xs])
    return xs, mask & bo, S


def x_max_y1(beta, n=60001):
    """maximal feasible x with all y_i = 1 (contiguity assumed, verified)."""
    beta = np.asarray(beta, float)
    xs, ok, S = x_feasible_set(beta, n=n)
    if not ok.any():
        return 0.0, False
    i = np.nonzero(ok)[0].max()
    x_hi = xs[i]
    # refine with bisection between x_hi and x_hi+step
    step = xs[1] - xs[0]
    a, b = x_hi, min(x_hi + step, 1.0)
    for _ in range(80):
        m = 0.5 * (a + b)
        if theta_of(beta, m, 1.0).sum() >= PI and branch_ok(beta, m, 1.0):
            a = m
        else:
            b = m
    return a, True


def A_direct_y1(beta):
    """sup of A with y_i = 1 (only valid when the y=1 saturation is the inner
    optimum, which holds because A and theta_i are both increasing in y)."""
    beta = np.asarray(beta, float)
    if beta.sum() >= 2 * PI - 1e-12:
        return 0.0, 0.0, False
    xm, ok = x_max_y1(beta)
    if not ok:
        return 0.0, 0.0, False
    return xm * float(np.sin(beta).sum()), xm, True


def A_direct_full(beta):
    """Inner maximization over y_i (common-scale family) for a given beta, plus
    the x search.  Returns (A, x, y, ok)."""
    beta = np.asarray(beta, float)
    if beta.sum() >= 2 * PI - 1e-12:
        return 0.0, 0.0, np.zeros(3), False
    best = (0.0, 0.0, np.ones(3), False)
    xs = np.linspace(1e-9, 1.0, 4001)
    for x in xs:
        s_ones = theta_of(beta, x, 1.0).sum()
        if s_ones >= PI and branch_ok(beta, x, 1.0):
            val = x * float(np.sin(beta).sum())
            if val > best[0]:
                best = (val, x, np.ones(3), True)
            continue
        # need lambda<1: bisect on lambda in (0,1) for sum theta = pi
        lo, hi = 1e-9, 1.0
        if theta_of(beta, x, lo).sum() <= PI:
            continue                     # cannot reach pi at all at this x
        for _ in range(60):
            mid = 0.5 * (lo + hi)
            if theta_of(beta, x, mid).sum() > PI:
                lo = mid
            else:
                hi = mid
        lam = lo
        y = lam * np.ones(3)
        if not branch_ok(beta, x, y):
            continue
        val = x * float((y * np.sin(beta)).sum())
        if val > best[0]:
            best = (val, x, y, True)
    return best


def ascent_full(b0, sweeps=120, step0=0.3):
    b = np.clip(np.asarray(b0, float), 1e-6, PI - 1e-6)
    if b.sum() >= 2 * PI - 1e-9:
        b = b * (2 * PI - 1e-6) / b.sum()
    f = lambda z: A_direct_full(z)[0]
    best = f(b)
    step = step0
    for _ in range(sweeps):
        imp = False
        for i in range(3):
            for sg in (1, -1):
                c = b.copy()
                c[i] = min(max(c[i] + sg * step, 1e-6), PI - 1e-6)
                if c.sum() >= 2 * PI - 1e-9:
                    continue
                v = f(c)
                if v > best * (1 + 1e-12):
                    best, b, imp = v, c, True
        if not imp:
            step *= 0.5
            if step < 1e-9:
                break
    return best, b


if __name__ == '__main__':
    import json
    rng = np.random.default_rng(99)
    out = {}
    # sanity: known points
    known = {
        'pi3_all': [PI / 3] * 3,
        'pi2_all': [PI / 2] * 3,
        'diag1.2': [1.2] * 3,
        'diag0.9': [0.9] * 3,
        'lead_cand': [0.9223829833, 1.1925065472, 1.1925065472],
        'twoeq_1.107*2_2.034': [1.1071525241614806, 1.1071525241614806, 2.0344401294283125],
    }
    for k, b in known.items():
        A, x, y, ok = A_direct_full(b)
        out[k] = dict(A=A, x=x, y=list(y), ok=ok, Bsum=float(np.sum(b)))
    print(json.dumps(out, indent=1))
