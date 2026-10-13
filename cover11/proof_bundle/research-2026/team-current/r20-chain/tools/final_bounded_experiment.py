"""r20-chain FINAL BOUNDED EXPERIMENT: global minimum of the cluster slack.

Criterion (sound, see the note):
  For every legal cover of the q0(6,7) class there is a split of the nine ring edges into
  two contiguous arcs (served by A and by B) such that for each hub
        cap_H(arc)  >=  width_H(arc),
  where cap_H(arc) = sum over the arc's edges of (s_H(c_i)+s_H(c_{i+1})),
        width_H(arc) = the signed ring turn at H over the arc (the angular width H spans),
  and s_H(c) = arccos(|H-c|/(2R)), defined only when |H-c| <= 2R (else cap = +inf, edge
  not servable by H).
  Define
        SLACK(R) := min over configurations of  max over splits of min(slack_A, slack_B).
  Any cover requires SLACK(R) >= 0 for its own split; a configuration is IMPOSSIBLE as soon
  as max over splits of min(slack_A,slack_B) < 0.
  Hence  max_{conf} max_{split} min(slack_A,slack_B) < 0  at radius R  ==>  r_D(11) > R.
  This script computes that maximum (over configurations) of the best split for a few R.
"""
import json, numpy as np
from pathlib import Path
from scipy.optimize import differential_evolution, minimize

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
OBJ = HERE.parent.parent / "cline2-sharp-fan" / "out" / "certified_object_copy.json"
log = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); log.append(s)

obj = json.loads(OBJ.read_text(encoding="utf-8"))
C = np.array([[int(a) / 1e17, int(b) / 1e17] for a, b in obj["centers_scaled_1e17"]])
Rc = float(obj["certified_interval"]["lo"])
HA, HB = C[0], C[2]
ID = np.array([1, 3, 4, 5, 6, 7, 8, 9, 10])
ring0 = C[ID]
o0 = np.argsort(np.arctan2(ring0[:, 1], ring0[:, 0])); ring0 = ring0[o0]

def spoke_s(H, ring, R):
    d = np.linalg.norm(ring - H, axis=1)
    s = np.full(len(ring), np.inf)
    m = d <= 2 * R
    s[m] = np.arccos(np.clip(d[m] / (2 * R), -1, 1))
    return s

def best_slack(ring, hA, hB, R):
    """max over the 9 splits of min(slack over A-arc, slack over B-arc). -inf if none works."""
    sA = spoke_s(hA, ring, R); sB = spoke_s(hB, ring, R)
    n = len(ring)
    nxt = np.roll(np.arange(n), -1)
    capA = sA + sA[nxt]; capB = sB + sB[nxt]
    def signed_turns(H):
        t = np.arctan2(*(ring - H).T)
        d = np.diff(np.append(t, t[0]))
        d[-1] = t[0] - t[-1]
        return d
    tA = signed_turns(hA); tB = signed_turns(hB)
    best = -np.inf
    for L in range(1, n):
        for e in range(n):
            arcA = [(e + k) % n for k in range(L)]
            arcB = [(e + L + k) % n for k in range(n - L)]
            if not np.all(np.isfinite(capA[arcA])):
                continue
            if not np.all(np.isfinite(capB[arcB])):
                continue
            slA = capA[arcA].sum() - tA[arcA].sum()
            slB = capB[arcB].sum() - tB[arcB].sum()
            best = max(best, min(slA, slB))
    return best

def neg_best(v, R):
    ring = v[0:18].reshape(9, 2); hA = v[18:20]; hB = v[20:22]
    if np.any(np.linalg.norm(ring, axis=1) > 1.0 + 1e-12): return 1e3
    if np.linalg.norm(hA) > 1 - R + 1e-12 or np.linalg.norm(hB) > 1 - R + 1e-12: return 1e3
    b = best_slack(ring, hA, hB, R)
    return 1e3 if not np.isfinite(b) else -b

P("certified R = %.17f" % Rc)
P("\n=== candidate calibration of the criterion ===")
x0 = np.concatenate([ring0.ravel(), HA, HB])
for R in (Rc, 0.38, 0.39, 0.40):
    b = best_slack(ring0, HA, HB, R)
    P(f"  R = {R:.7f}:  candidate best-split slack = {b:+.8f}   ({'OK (>=0)' if b >= 0 else 'VIOLATED'})")

P("\n=== global maximisation of the best-split slack ===")
def opt(R, seeds=(0, 1, 2), budget=(160, 16)):
    bounds = [(-1, 1)] * 18 + [(-(1 - R), 1 - R)] * 4
    best, bx = -1e9, x0
    for s in seeds:
        rng = np.random.default_rng(s)
        start = np.concatenate([rng.uniform(-1, 1, 18), rng.uniform(-(1 - R), 1 - R, 4)])
        res = differential_evolution(neg_best, bounds, args=(R,), seed=s, maxiter=budget[0],
                                     tol=1e-10, popsize=budget[1], mutation=(0.3, 1.2),
                                     recombination=0.9, polish=True, init='sobol', updating='deferred')
        if -res.fun > best:
            best, bx = -res.fun, res.x
    r2 = minimize(neg_best, bx, args=(R,), method='Nelder-Mead',
                  options=dict(maxiter=60000, maxfev=120000, xatol=1e-13, fatol=1e-15))
    if -r2.fun > best:
        best, bx = -r2.fun, r2.x
    return best, bx

summ = {}
for R in (0.38, 0.385, 0.39, 0.395, 0.40, 0.41):
    b, x = opt(R)
    ring = x[0:18].reshape(9, 2); hA = x[18:20]; hB = x[20:22]
    summ[R] = b
    P(f"  R = {R:.7f}:  max over configurations of the best-split slack = {b:+.8f}"
      f"   {'*** ALL CONFIGURATIONS EXCLUDED (max < 0) ***' if b < 0 else 'not excluded'}")
    P(f"              argmax |hA|={np.linalg.norm(hA):.5f} |hB|={np.linalg.norm(hB):.5f}"
      f"  ring radii {np.round(np.linalg.norm(ring,axis=1),5)}")

(OUT / "final_bounded_experiment.json").write_text(json.dumps(
    {"certified_R": Rc, "max_best_slack": {str(k): float(v) for k, v in summ.items()}}, indent=1))
(OUT / "final_bounded_experiment.txt").write_text("\n".join(log) + "\n")
P("\nwrote " + str(OUT / "final_bounded_experiment.txt"))
