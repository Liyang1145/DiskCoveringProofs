"""
Ground-truth 2-D search, no case logic.

Parameterise by x in (0,1] and theta_i in (0, pi-beta_i) with sum theta_i = pi
(theta_1, theta_2 free on a triangular grid, theta_3 = pi-theta_1-theta_2).
For each triple (x, theta) solve the chord identity for y_i:
    tan theta_i = y_i sin b_i / (x - y_i cos b_i)
  =>  y_i = x tan theta_i / (sin b_i + cos b_i tan theta_i)
and require 0 < y_i <= 1.  Objective A = x sum_i y_i sin b_i.
This is a direct, exhaustive check of the relaxation over (x, theta).
"""
import json
import sys
import numpy as np
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import envelope_clean as EC

PI = EC.PI


def best_A(beta, nx=301, nth=301):
    beta = np.asarray(beta, float)
    s = np.sin(beta)
    c = np.cos(beta)
    t1 = np.linspace(1e-6, PI - 1e-6, nth)
    best = (0.0, None, None)
    for x in np.linspace(1.0, 1e-6, nx):
        # grid over (theta1, theta2) with theta3 = pi - th1 - th2
        T1, T2 = np.meshgrid(t1, t1, indexing='ij')
        T3 = PI - T1 - T2
        m = (T3 > 1e-6) & (T3 < PI - 1e-6)
        T = [T1[m], T2[m], T3[m]]
        okmask = np.ones_like(T[0], dtype=bool)
        y = []
        for i in range(3):
            ti = T[i]
            if ti.max() >= PI - beta[i] - 1e-12:
                okmask &= (ti < PI - beta[i] - 1e-12)
            den = s[i] + c[i] * np.tan(ti)
            yi = x * np.tan(ti) / den
            okmask &= (yi > 0) & (yi <= 1 + 1e-12)
            y.append(yi)
        if not okmask.any():
            continue
        A = x * sum(y[i] * s[i] for i in range(3))
        A = np.where(okmask, A, -1.0)
        k = int(np.argmax(A))
        if A[k] > best[0]:
            best = (float(A[k]), float(x),
                    [float(T[0][k]), float(T[1][k]), float(T[2][k])])
    return best


if __name__ == '__main__':
    import time
    cases = {'pi3': [PI / 3] * 3, 'pi2': [PI / 2] * 3, '1.2': [1.2] * 3,
             'cand': [0.9223829833, 1.1925065472, 1.1925065472],
             '1.0': [1.0] * 3}
    out = {}
    for k, b in cases.items():
        t0 = time.time()
        v, x, th = best_A(b, nx=161, nth=241)
        env = float(EC.A_of_beta(np.asarray(b).reshape(3, 1), 'theorem')[0][0])
        out[k] = dict(beta=list(b), best=v, x=x, theta=th, envelope=env,
                      envelope_feasible=(v <= env + 1e-9), secs=time.time() - t0)
        print(k, 'best=%.9f' % v, 'at x=%.5f' % x, 'theta=', np.round(th, 4),
              'envelope=%.9f' % env, 'env bound ok=', v <= env + 1e-9,
              '%.1fs' % (time.time() - t0), flush=True)
    with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\ground_truth_scan.json", 'w') as f:
        json.dump(out, f, indent=1)
