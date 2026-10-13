"""Push a violating configuration below the campaign threshold U by coordinate descent on the
covering radius, keeping the nesting violation (which is an open condition)."""
import json, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records

U = 0.33173203427623414

xs = np.linspace(-1, 1, 420)
X, Y = np.meshgrid(xs, xs)
keep = X ** 2 + Y ** 2 <= 1.0
GRID = np.stack([X[keep], Y[keep]], 1)
print("grid points:", len(GRID))

def radius(S):
    d = np.linalg.norm(GRID[:, None, :] - S[None, :, :], axis=2)
    mn = d.min(1)
    idx = np.argsort(mn)[-4:]
    best = float(mn[idx[-1]])
    for i0 in idx:
        x = GRID[i0].copy(); step = 0.01
        for _ in range(80):
            cand = np.array([[x[0] + dx, x[1] + dy] for dx in (-step, 0, step) for dy in (-step, 0, step)])
            cand = cand[(cand ** 2).sum(1) <= 1.0]
            vals = np.linalg.norm(cand[:, None, :] - S[None, :, :], axis=2).min(1)
            j = int(np.argmax(vals))
            if vals[j] > best:
                best = float(vals[j]); x = cand[j]
            else:
                step *= 0.5
                if step < 1e-12: break
    return best

def viol(S):
    recs, anch = anchor_records(S)
    if not recs: return None, None
    mn = min(min(r["nest_ccw"], r["nest_cw"]) for r in recs)
    mx = max(abs(r["resid"]) for r in recs)
    return mn, mx

def descend(S0, iters=14, verbose=True):
    S = S0.copy()
    f = radius(S)
    for it in range(iters):
        h = 0.02 / (1 + it)
        improved = False
        for i in range(len(S)):
            for ang in np.linspace(0, 2 * math.pi, 8, endpoint=False):
                cand = S.copy()
                cand[i] = S[i] + h * np.array([math.cos(ang), math.sin(ang)])
                if (cand[i] ** 2).sum() > 1.0:
                    continue
                fv = radius(cand)
                if fv < f - 1e-15:
                    S, f = cand, fv; improved = True
        if verbose:
            mn, mx = viol(S)
            print(f"  pass {it}: r={f:.10f} min_nest={mn:+.3e} max|resid|={mx:.2e} improved={improved}")
        if not improved and it > 3:
            break
    return S, f

if __name__ == "__main__":
    cand = np.array([[float(__import__("fractions").Fraction(x)) for x in p]
                     for p in json.loads((HERE.parent.parent / "lead" / "improved-upper-test.json")
                                         .read_text())["centers"]])
    cfgs = json.loads((HERE / "violating-configs.json").read_text())
    print("\n[control] coordinate descent from the campaign candidate")
    Sc, fc = descend(cand)
    mnc, mxc = viol(Sc)
    print(f"  -> r={fc:.10f} min_nest={mnc:+.3e} max|resid|={mxc:.2e}")
    print("\n[main] coordinate descent from the violating configuration")
    S0 = np.array(cfgs[0]["sites"])
    print("  start r =", f"{radius(S0):.10f}", "min_nest =", f"{viol(S0)[0]:+.3e}", " U =", U)
    S1, f1 = descend(S0)
    mn1, mx1 = viol(S1)
    print(f"  -> r={f1:.10f}  (U={U:.10f}, r-U={f1-U:+.3e})  min_nest={mn1:+.3e} max|resid|={mx1:.3e}")
    out = dict(r=float(f1), U=float(U), min_nest=float(mn1), max_resid=float(mx1),
               sites=S1.tolist())
    (HERE / "pushed-config.json").write_text(json.dumps(out, indent=1))
    print("  saved pushed-config.json")
