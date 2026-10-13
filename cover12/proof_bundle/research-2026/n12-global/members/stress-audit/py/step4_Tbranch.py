"""stress-audit step 4: is T=0 an extra condition on the F=G=H branch?

T was shown NOT to lie in the ideal <F,G,H> by groebner normal form (step3).
That still leaves two possibilities for the branch through the recorded root:
  (i)  T vanishes identically on that irreducible branch (then T in the radical,
       T=0 is automatic and the conditional hypothesis is the FGH curve);
  (ii) T cuts the branch at an isolated point (a genuine 4th equation); then the
       zero must be shown to lie in the verified box.
Predictor-corrector continuation on the FGH curve decides, and also measures the
distance from the box centre to the T-zero.
"""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 60
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
J = json.loads((ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json").read_text(encoding="utf-8"))
a0, t0, r0, w0 = [mp.mpf(s) for s in J["root"]]

def fgh(a, t, r, w):
    b = (1 + a + r) / 2
    F = t * t - 2 * t * r - a * t + a * r + a * a
    G = (1 + t * t - r * r) * (3 * b * b + w * w) - t * (3 * b * b - w * w + 6 * b * w)
    H = 4 * w * w - 12 * r * r + 3 * (1 - a - r) ** 2
    return mp.matrix([F, G, H])

def Tval(a, t, r, w):
    b = (1 + a + r) / 2
    S = b * b + w * w / 3
    A = 3 * b * b - w * w - 2 * b * w
    return w * S * S * (2 * a - t + r) * (1 - t * t - r * r) + (S - b) * (2 * t - 2 * r - a) * t * t * A

x0 = mp.matrix([a0, t0, r0, w0])
Jac = mp.matrix(3, 4)
for i, v in enumerate(x0):
    e = mp.matrix([0, 0, 0, 0]); e[i] = mp.mpf('1e-25')
    Jac[:, i] = (fgh(*(x0 + e)) - fgh(*(x0 - e))) / (2 * mp.mpf('1e-25'))
def newton(x):
    for _ in range(30):
        F = fgh(*x)
        Jx = mp.matrix(3, 4)
        for i in range(4):
            e = mp.matrix([0, 0, 0, 0]); e[i] = mp.mpf('1e-30')
            Jx[:, i] = (fgh(*(x + e)) - fgh(*(x - e))) / (2 * mp.mpf('1e-30'))
        # minimum-norm correction: dx = -J^T (J J^T)^{-1} F
        dx = -Jx.T * (Jx * Jx.T) ** -1 * F
        x = x + dx
        if max(abs(c) for c in F) < mp.mpf('1e-120'):
            break
    return x

# tangent direction of the FGH curve at the root
Jx0 = mp.matrix(3, 4)
for i in range(4):
    e = mp.matrix([0, 0, 0, 0]); e[i] = mp.mpf('1e-30')
    Jx0[:, i] = (fgh(*(x0 + e)) - fgh(*(x0 - e))) / (2 * mp.mpf('1e-30'))
sv = mp.svd(Jx0, compute_uv=False)
print("singular values of dFGH:", [mp.nstr(s, 8) for s in sv])
G4 = Jx0.T * Jx0
ev, evec = mp.eigsy(G4)
print("eigenvalues of J^T J:", [mp.nstr(v, 8) for v in ev])
tang = evec[:, 0]
print("tangent direction:", [mp.nstr(c, 12) for c in tang])
print("|Jx0 * tang| =", mp.nstr(max(abs(c) for c in (Jx0 * tang)), 6))

print("\n s          |FGH|_inf        T(s)")
for s in ['0', '1e-30', '1e-20', '1e-12', '1e-8', '1e-6', '1e-4', '1e-3']:
    sm = mp.mpf(s)
    x = newton(x0 + sm * tang)
    print(f"  {s:>8}  {mp.nstr(max(abs(c) for c in fgh(*x)),6):>12}  {mp.nstr(Tval(*x),12)}")

# also: a far point on the FGH curve, to see T there (checks T not in the ideal)
for s in ['0.5', '1.0']:
    x = newton(x0 + mp.mpf(s) * tang)
    print(f"  far {s}: T = {mp.nstr(Tval(*x),12)}  |FGH| = {mp.nstr(max(abs(c) for c in fgh(*x)),6)}")
