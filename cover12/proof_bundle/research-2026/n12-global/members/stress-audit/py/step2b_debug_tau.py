"""stress-audit debug: anchor-0 tangential components, all pieces printed."""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps = 50
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
J = json.loads((ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json").read_text(encoding="utf-8"))
a, t, r, w = [mp.mpf(s) for s in J["root"]]
b = (1 + a + r) / 2
v = w / mp.sqrt(3)
S = b * b + v * v
d = a + r
beta = mp.atan2(v, b)
al = mp.pi / 3 - 2 * beta

P = mp.matrix([mp.cos(2 * beta), mp.sin(2 * beta)])
tau = mp.matrix([-P[1], P[0]])
s0 = mp.matrix([b, v])
s1 = mp.matrix([t * mp.cos(mp.pi / 3), t * mp.sin(mp.pi / 3)])
print("shape P:", P.rows, P.cols, " P[0],P[1] =", mp.nstr(P[0], 20), mp.nstr(P[1], 20))
print("|P| =", mp.nstr(mp.sqrt(P[0] ** 2 + P[1] ** 2), 20))
print("(s0-P).tau =", mp.nstr((s0 - P)[0] * tau[0] + (s0 - P)[1] * tau[1], 20), "   -b sin(beta) =", mp.nstr(-b * mp.sin(beta), 20))
print("(s1-P).tau =", mp.nstr((s1 - P)[0] * tau[0] + (s1 - P)[1] * tau[1], 20), "   +t sin(alpha) =", mp.nstr(t * mp.sin(al), 20))
print("cos(beta) =", mp.nstr(mp.cos(beta), 20), " b/s =", mp.nstr(b / mp.sqrt(S), 20))
print("sin(beta) =", mp.nstr(mp.sin(beta), 20), " v/s =", mp.nstr(v / mp.sqrt(S), 20))
print("t sin(alpha) vs y v / z ratio:")
y = (b - 1) * S / (S - b)
jj = None
q = 2 * (1 - b) / r
uu = q * r / (2 * a - t + r)
jj = uu * (2 * t - 2 * r - a) / r
zz = jj * r * t / (1 - t * t - r * r)
print("   z t sin(alpha) =", mp.nstr(zz * t * mp.sin(al), 20), "  y v =", mp.nstr(y * v, 20), "  y b sin(beta) =", mp.nstr(y * b * mp.sin(beta), 20))
print("   (s0-P).tau - (-b sin beta) =", mp.nstr(((s0 - P)[0] * tau[0] + (s0 - P)[1] * tau[1]) + b * mp.sin(beta), 20))
# angle check
print("arg(s0) =", mp.nstr(mp.atan2(v, b), 20), " 2beta =", mp.nstr(2 * beta, 20), " arg(P) =", mp.nstr(mp.atan2(P[1], P[0]), 20))
print("arg(s1) =", mp.nstr(mp.atan2(s1[1], s1[0]), 20))
