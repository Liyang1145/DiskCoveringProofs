"""
FULLY corrected maximization of the shared-face relaxation.

    max  A = x * sum_i y_i sin beta_i
    s.t. beta in (0,pi)^3, Bsum = sum beta_i < 2pi, 0 < x <= 1, 0 < y_i <= 1,
         sum_i theta_i = pi,   0 < theta_i < pi - beta_i,
         theta_i = atan2(y_i sin beta_i, x - y_i cos beta_i).

For fixed beta the feasible x-set is an interval whose upper end is
    x_hi(beta) = min(1, min_i x_i^bound(beta_i))
where x_i^bound is where theta_i would hit pi - beta_i with y_i = 1, i.e.
    theta_i(x,1) = pi - beta_i        (for beta_i < pi/2 there is no bound).
At x = x_hi the value is
    A(x_hi, y_hi(beta))  with y_hi = largest common scale lambda in (0,1] such
    that sum_i theta_i(x_hi, lambda) = pi  (exist iff sum_i theta_i(x_hi,1)>=pi;
    if not, smaller x gives larger sums).
A is increasing in x, so the inner maximum over x is at x_hi (verified by
1-D scan). The inner maximum over y is at a boundary of the box; using the
common-scale family is justified because A and every theta_i increase in y_i.

This module returns A_inner(beta) = max over x,y for that beta; then a global
search over beta gives the sharp constant.  No algebraic envelope formula is
used anywhere.
"""
import numpy as np

PI = float(np.pi)


def theta(beta, x, y):
    beta = np.asarray(beta, float)
    y = np.broadcast_to(np.asarray(y, float), beta.shape)
    num = y * np.sin(beta)
    den = x - y * np.cos(beta)
    th = np.arctan2(num, den)
    return np.where(th < 0, th + 2 * PI, th)


def theta_ok(beta, x, y, tol=1e-13):
    """0 < theta_i < pi - beta_i for all i, and 0<=x,y<=1."""
    if x <= 0 or x > 1 + 1e-15:
        return False
    yarr = np.asarray(y, float)
    if np.any(yarr <= 0) or np.any(yarr > 1 + 1e-15):
        return False
    beta = np.asarray(beta, float)
    th = theta(beta, x, y)
    return bool(np.all(th > 0) and np.all(th < (PI - beta) - tol))


def inner_max(beta, nx=241, refine=60):
    """max over x in (0,1] of the best y-value A, for one beta."""
    beta = np.asarray(beta, float)
    Bsum = beta.sum()
    if Bsum >= 2 * PI - 1e-12 or np.any(beta <= 0) or np.any(beta >= PI):
        return 0.0, 0.0, np.zeros(3)
    one = np.ones(3)
    xs = np.linspace(1e-6, 1.0, nx)
    best = (0.0, 0.0, one.copy())

    def value_at(x):
        # best y (in the common-scale family) with sum theta = pi
        g1 = theta(beta, x, one).sum()
        if theta_ok(beta, x, one) and g1 >= PI:
            y = one.copy()
            return x * float(np.sin(beta).sum()), y
        # bisect lambda
        lo, hi = 1e-12, 1.0
        if theta(beta, x, lo * one).sum() <= PI:
            return None, None
        for _ in range(80):
            mid = 0.5 * (lo + hi)
            if theta(beta, x, mid * one).sum() > PI:
                lo = mid
            else:
                hi = mid
        lam = lo
        y = lam * one
        if not theta_ok(beta, x, y):
            return None, None
        return x * float((y * np.sin(beta)).sum()), y

    for x in xs:
        v, y = value_at(x)
        if v is not None and v > best[0]:
            best = (v, x, y.copy())
    # local refine around best x
    if best[1] > 0:
        step = xs[1] - xs[0]
        x = best[1]
        for _ in range(refine):
            improved = False
            for sg in (1, -1):
                xn = min(max(x + sg * step, 1e-9), 1.0)
                v, y = value_at(xn)
                if v is not None and v > best[0]:
                    best, x, improved = (v, xn, y.copy()), xn, True
            if not improved:
                step *= 0.5
                if step < 1e-12:
                    break
    return best


def global_search(seed=2027, n_restart=250, nx=161):
    rng = np.random.default_rng(seed)
    starts = [[PI / 3] * 3, [PI / 2] * 3, [1.0] * 3, [1.4, 1.28, 0.5],
              [1.3, 1.3, 1.3], [0.9, 1.2, 1.2], [2.0, 0.55, 0.55],
              [1.5, 1.4, 0.4], [1.45, 1.2, 0.6], [1.05] * 3,
              [PI - 0.05, 0.05, 0.05], [1.6, 1.0, 0.6]]
    best = (-1.0, None, None, None)
    for s in starts:
        s = np.asarray(s, float)
        if s.sum() >= 2 * PI - 1e-9:
            continue
        v = inner_max_beta(s, nx=nx)
        if v[0] > best[0]:
            best = (v[0], s, v[1], v[2])
    for _ in range(n_restart):
        u = np.clip(rng.dirichlet(np.ones(3)) * rng.uniform(0.3, 6.2), 1e-6, PI - 1e-6)
        if u.sum() >= 2 * PI - 1e-9:
            u = u * (2 * PI - 1e-6) / u.sum()
        v = inner_max_beta(u, nx=nx)
        if v[0] > best[0]:
            best = (v[0], u, v[1], v[2])
    return best


def inner_max_beta(beta, nx=161):
    v, x, y = inner_max(beta, nx=nx)
    return v, x, y


if __name__ == '__main__':
    import json
    pts = {'pi3': [PI / 3] * 3, 'pi2': [PI / 2] * 3, '1.2': [1.2] * 3,
           'hand1.4_1.28_0.5': [1.4, 1.28, 0.5], 'lead_cand': [0.9223829833, 1.1925065472, 1.1925065472],
           'diag1.1': [1.1] * 3, '1.3_1.3_1.3': [1.3] * 3}
    for k, b in pts.items():
        v, x, y = inner_max(np.asarray(b, float))
        print(k, b, 'Bsum=%.6f' % np.sum(b), 'A=%.12f' % v, 'x=%.8f' % x,
              'y=', np.round(y, 6))
