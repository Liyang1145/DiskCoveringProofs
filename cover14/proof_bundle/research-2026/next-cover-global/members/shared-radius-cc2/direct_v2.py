"""
CORRECTED (v2) direct maximization of the shared-face relaxation.

    max  A = x * sum_i y_i sin beta_i
    s.t. beta_i in (0,pi), Bsum = sum beta_i < 2pi, 0 < x <= 1, 0 < y_i <= 1,
         sum_i theta_i = pi,  0 < theta_i < pi - beta_i,
         theta_i = atan2(y_i sin beta_i, x - y_i cos beta_i).

Constraint geometry used (THREE structural cases, determined at y = 1):
  S(x) := sum_i theta_i(x, 1)   is strictly decreasing in x on (0,1].
  * S(1) = pi exactly  -> x0 = 1 is feasible with y = 1 (junction).
  * S(1) <  pi         -> the y = 1 point is below the required total; since
                          raising y raises each theta_i, the value pi is
                          reached at some lambda > 1 or not at all, so the y=1
                          cap is INACTIVE and the max over y is on the box
                          boundary; the inner optimum is at x = x0 (the crossing
                          of S through pi) with y = 1.
  * S(1) >  pi         -> y = 1 overshoots; the feasible y are those with
                          y_i <= y_i^max where theta_i(x, y_i) = pi - beta_i
                          would be violated, and the sum constraint is met by
                          scaling down.  The optimum is on the boundary of the
                          branch constraint and/or the box.
The module returns inner_max(beta) = max over (x,y) and records which case fired.
"""
import numpy as np

PI = float(np.pi)


def theta(beta, x, y):
    beta = np.asarray(beta, float)
    y = np.broadcast_to(np.asarray(y, float), beta.shape)
    th = np.arctan2(y * np.sin(beta), x - y * np.cos(beta))
    return np.where(th < 0, th + 2 * PI, th)


def branch_ok(beta, x, y, tol=1e-13):
    """0 < theta_i < pi - beta_i (per-component) and 0<=x,y<=1."""
    if not (0 < x <= 1 + 1e-15):
        return False
    yarr = np.asarray(y, float)
    if np.any(yarr <= 0) or np.any(yarr > 1 + 1e-15):
        return False
    beta = np.asarray(beta, float)
    th = theta(beta, x, y)
    return bool(np.all(th > 0) and np.all(th < (PI - beta) - tol))


def S1(beta):
    return float(theta(np.asarray(beta, float), 1.0, np.ones(3)).sum())


def x0_cross(beta, iters=120):
    """crossing of S through pi in (0,1]; x0=1 if S(1)>=pi, None impossible
    because S(0+)=3pi-Bsum>pi whenever Bsum<2pi."""
    beta = np.asarray(beta, float)
    if S1(beta) >= PI:
        return 1.0
    lo, hi = 1e-13, 1.0
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if theta(beta, mid, np.ones(3)).sum() > PI:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def inner_max(beta, nx=1201):
    """max over x in (0,1] of the best feasible A for this beta.

    Structure: S(x)=sum theta_i(x,1) decreases from 3pi-Bsum to S(1).
    Crossing x0 in (0,1] always exists.  y=1 is optimal for fixed x
    (theta_i and A both increase in y_i; the branch bound allows y=1).
    Two cases:
      S(1) <= pi  ->  feasible x in (0,x0], value at x0 with y=1;
      S(1) >  pi  ->  x=x0 overshoots the branch bound; the feasible x are
                      those > x0 with theta_i(x,1) < pi-beta_i, and the value
                      is x*sum sin beta_i maximised at the largest such x <= 1.
    """
    beta = np.asarray(beta, float)
    if beta.sum() >= 2 * PI - 1e-12 or np.any(beta <= 0) or np.any(beta >= PI):
        return dict(A=0.0, x=0.0, y=np.zeros(3), case='infeasible-domain')
    one = np.ones(3)
    s1 = S1(beta)
    x0 = x0_cross(beta)
    if x0 is None:
        return dict(A=0.0, x=0.0, y=one.copy(), case='no-crossing')
    if s1 <= PI + 1e-14:
        if branch_ok(beta, x0, one):
            return dict(A=x0 * float(np.sin(beta).sum()), x=x0, y=one.copy(),
                        case='junction' if abs(s1 - PI) < 1e-12 else 'lower(x0,y1)')
        return dict(A=0.0, x=0.0, y=one.copy(), case='lower-branch-violated')
    # s1 > pi: feasible x are x in (x0, 1] with branch ok; value grows with x
    xs = np.linspace(1.0, x0, 4001)[1:]
    best = dict(A=0.0, x=0.0, y=one.copy(), case='upper-none')
    for x in xs:
        if branch_ok(beta, x, one):
            best = dict(A=x * float(np.sin(beta).sum()), x=x, y=one.copy(),
                        case='upper(y1)')
            break
    return best


def global_search(seed=2027, n_restart=200, nx=401):
    rng = np.random.default_rng(seed)
    starts = [[PI / 3] * 3, [PI / 2] * 3, [1.0] * 3, [1.4, 1.28, 0.5],
              [1.3] * 3, [0.9, 1.2, 1.2], [2.0, 0.55, 0.55], [1.5, 1.4, 0.4],
              [1.45, 1.2, 0.6], [1.05] * 3, [PI - 0.05, 0.05, 0.05], [1.6, 1.0, 0.6],
              [PI / 4] * 3, [1.15] * 3, [0.8] * 3]
    best = (-1.0, None, None)
    for s in starts:
        s = np.asarray(s, float)
        if s.sum() >= 2 * PI - 1e-9:
            continue
        r = inner_max(s, nx=nx)
        if r['A'] > best[0]:
            best = (r['A'], s, r)
    for _ in range(n_restart):
        u = np.clip(rng.dirichlet(np.ones(3)) * rng.uniform(0.3, 6.2), 1e-6, PI - 1e-6)
        if u.sum() >= 2 * PI - 1e-9:
            u = u * (2 * PI - 1e-6) / u.sum()
        r = inner_max(u, nx=nx)
        if r['A'] > best[0]:
            best = (r['A'], u, r)
    return best


if __name__ == '__main__':
    import json
    pts = {'pi3': [PI / 3] * 3, 'pi4': [PI / 4] * 3, 'pi2': [PI / 2] * 3,
           '1.0^3': [1.0] * 3, '1.2^3': [1.2] * 3, '1.3^3': [1.3] * 3,
           'lead_cand': [0.9223829833, 1.1925065472, 1.1925065472],
           '1.4,1.28,0.5': [1.4, 1.28, 0.5]}
    for k, b in pts.items():
        r = inner_max(np.asarray(b, float), nx=2001)
        print(k, 'Bsum=%.5f' % np.sum(b), 'S(1)=%.5f' % S1(b),
              'A=%.9f' % r['A'], 'x=%.6f' % r['x'], r['case'],
              'y=', np.round(r['y'], 4))
