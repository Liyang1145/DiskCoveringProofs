"""
Clean scan of the relaxation, no case-logic shortcuts:

    max  A = x * sum_i y_i sin beta_i   over 0<x<=1, 0<y_i<=1
    s.t. sum_i theta_i(x,y) = pi ,  0 < theta_i < pi - beta_i
    theta_i = atan2(y_i sin b_i, x - y_i cos b_i)

For each x in a grid we find y_i by bisecting a common scale lambda in (0,1]
with S(x,lambda) := sum_i theta_i(x, lambda) = pi  (S is decreasing in lambda),
and we also test the general box: y_i = min(1, lambda_i) families.
Report f(beta) = max over the grid, plus which (x,y) attained it.
"""
import json
import sys
import numpy as np
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import envelope_clean as EC

PI = EC.PI


def theta(beta, x, y):
    beta = np.asarray(beta, float)
    y = np.broadcast_to(np.asarray(y, float), beta.shape)
    th = np.arctan2(y * np.sin(beta), x - y * np.cos(beta))
    return np.where(th < 0, th + 2 * PI, th)


def S(beta, x, y):
    return float(theta(beta, x, y).sum())


def ok(beta, x, y, tol=1e-12):
    beta = np.asarray(beta, float)
    th = theta(beta, x, y)
    return bool(np.all(th > 0) and np.all(th < PI - beta - tol))


def solve_lambda(beta, x, iters=200):
    """largest lambda in (0,1] with S(x, lambda) = pi, or None."""
    if not (0 < x <= 1):
        return None
    s1 = S(beta, x, np.ones(3))
    if abs(s1 - PI) < 1e-13:
        return 1.0
    lo, hi = 1e-14, 1.0
    slo, shi = S(beta, x, lo), S(beta, x, hi)
    if not (slo > PI >= shi):
        return None
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if S(beta, x, mid) > PI:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def f(beta, n=4001):
    beta = np.asarray(beta, float)
    best = (0.0, None, None, None)
    for x in np.linspace(1.0, 1e-6, n):
        lam = solve_lambda(beta, x)
        if lam is None:
            continue
        y = lam * np.ones(3)
        if not ok(beta, x, y):
            continue
        v = x * float((y * np.sin(beta)).sum())
        if v > best[0]:
            best = (v, x, y, 'common-scale')
        # also try box family y_i = min(1, mu_i) with theta_i = pi-beta_i bounds
    # pure box family: y_i = min(1, c_i * lam) with c_i chosen so
    # theta_i hits pi - beta_i simultaneously is impossible in general;
    # try y_i = lam (done) and y_i = 1 for the icons with S<=pi
    for x in np.linspace(1.0, 1e-6, 401):
        sy = S(beta, x, np.ones(3))
        if sy <= PI and ok(beta, x, np.ones(3)):
            v = x * float(np.sin(beta).sum())
            if v > best[0]:
                best = (v, x, np.ones(3), 'y=1')
    return best


if __name__ == '__main__':
    cases = {'pi3': [PI / 3] * 3, 'pi4': [PI / 4] * 3, 'pi2': [PI / 2] * 3,
             '1.0': [1.0] * 3, '1.2': [1.2] * 3, '1.3': [1.3] * 3,
             'cand': [0.9223829833, 1.1925065472, 1.1925065472],
             '1.4_1.28_0.5': [1.4, 1.28, 0.5]}
    out = {}
    for k, b in cases.items():
        b = np.array(b)
        v, x, y, how = f(b, n=2001)
        env = float(EC.A_of_beta(b.reshape(3, 1), 'theorem')[0][0])
        x0 = float(EC.x0_theorem(b))
        out[k] = dict(beta=b.tolist(), Bsum=float(b.sum()), S1=S(b, 1.0, np.ones(3)),
                      f=v, x=x, y=None if y is None else y.tolist(), how=how,
                      envelope=env, x0=x0)
        print(k, 'S(1)=%.4f' % out[k]['S1'], 'x0=%.6f' % x0,
              'f=%.9f' % v, 'x=%.6f' % (x if x else 0), how,
              'envelope=%.9f' % env, 'ratio=%.6f' % (v / env if env else 0), flush=True)
    with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\clean_scan.json", 'w') as fh:
        json.dump(out, fh, indent=1)
