"""
FINAL corrected inner maximization (v3).

    max A = x * sum_i y_i sin b_i   over 0<x<=1, 0<y_i<=1
    s.t. sum_i theta_i(x,y) = pi ,  0 < theta_i < pi - b_i,
         theta_i = atan2(y_i sin b_i, x - y_i cos b_i).

Structure (verified numerically in audit_ground_truth.py and by S(x) tables):
  * theta_i increases in x at y=1, and increases in y_i for x < y_i cos b_i.
  * F(x,lam) := sum_i theta_i(x, lam*1) is strictly decreasing in lam on the
    branch-valid region (for x=1, beta=pi/2 exactly: F = 3*atan2(1,1) = 3pi/4).
  * crossing x0 solves S(x,1) = pi with S decreasing in x.
  * CASE Sigma beta <= pi  (=> S(1) <= pi): crossing x0 < 1; feasible y=1 for
    x <= x0 with total >= pi; to hit exactly pi we RAISE lam above 1 or run to
    lam=1 at x=x0.  Value = x0 * Sigma sin b.
  * CASE Sigma beta > pi   (=> S(1) > pi): lam=1 gives total > pi at x=1;
    lambda_min(x) = the lam with F(x,lam) = pi; feasible y = lam (>= lam_min).
    Objective lam * Sigma sin b is maximised by the LARGEST feasible lam <= 1,
    i.e. lam = 1 whenever lam_min <= 1, giving x * Sigma sin b, maximised at
    x=1: value = Sigma sin b.
So f(beta) = x0*Sigma sin b if Sigma beta <= pi, else Sigma sin b, in both cases
<= x0*Sigma sin b and <= 3sqrt3/2 for Sigma beta >= pi.
"""
import numpy as np

PI = float(np.pi)


def theta(beta, x, y):
    beta = np.asarray(beta, float)
    y = np.broadcast_to(np.asarray(y, float), beta.shape)
    th = np.arctan2(y * np.sin(beta), x - y * np.cos(beta))
    return np.where(th < 0, th + 2 * PI, th)


def S(beta, x, lam=1.0):
    return float(theta(beta, x, lam * np.ones(3)).sum())


def branch_ok(beta, x, y, tol=1e-12):
    beta = np.asarray(beta, float)
    th = theta(beta, x, y)
    return bool(np.all(th > 0) and np.all(th < PI - beta - tol))


def x0(beta, iters=200):
    beta = np.asarray(beta, float)
    if S(beta, 1.0) >= PI:
        return 1.0
    lo, hi = 1e-14, 1.0
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if S(beta, mid) > PI:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def lam_min(beta, x, iters=200):
    """smallest lam>0 with S(x,lam) = pi, or None if S(x,1) > pi already."""
    if S(beta, x, 1.0) <= PI:
        return 1.0
    lo, hi = 1e-14, 1.0
    slo = S(beta, x, lo)
    if slo <= PI:
        return None
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if S(beta, x, mid) > PI:
            lo = mid
        else:
            hi = mid
    return lo


def f(beta, n=2001):
    beta = np.asarray(beta, float)
    if beta.sum() >= 2 * PI - 1e-12 or np.any(beta <= 0) or np.any(beta >= PI):
        return dict(A=0.0, x=None, y=None, case='infeasible')
    xc = x0(beta)
    best = (0.0, None, None, 'none')
    for x in np.linspace(xc, 1.0, n):
        lm = lam_min(beta, x)
        if lm is None:
            continue
        y = lm * np.ones(3)
        if not branch_ok(beta, x, y):
            continue
        v = x * lmmul(y, beta)
        if v > best[0]:
            case = 'y=1' if abs(lm - 1) < 1e-12 else 'lam<1'
            best = (v, x, y, case)
    return dict(A=best[0], x=best[1], y=best[2], case=best[3], x0=xc)


def lmmul(y, beta):
    return float((np.asarray(y) * np.sin(np.asarray(beta))).sum())


if __name__ == '__main__':
    cases = {'pi3': [PI / 3] * 3, 'pi2': [PI / 2] * 3, '1.0': [1.0] * 3,
             '1.2': [1.2] * 3, '1.3': [1.3] * 3, 'pi4': [PI / 4] * 3,
             'cand': [0.9223829833, 1.1925065472, 1.1925065472],
             '1.4_1.28_0.5': [1.4, 1.28, 0.5]}
    for k, b in cases.items():
        r = f(b)
        print(k, 'Bsum=%.4f' % np.sum(b), 'S(1)=%.4f' % S(b, 1.0),
              'x0=%.6f' % r['x0'], 'A=%.9f' % r['A'],
              'x=%s' % (None if r['x'] is None else '%.6f' % r['x']), r['case'])
