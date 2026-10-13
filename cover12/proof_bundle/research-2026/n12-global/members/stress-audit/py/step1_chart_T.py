"""stress-audit step 1 (INDEPENDENT): does the recorded calibration root satisfy T=0?

Object: evidence/d3-chart-calibration.json (lead). Variables (a,t,r,w).
F,G,H as recorded; T as sent to candidate (lead/EXACT-CANDIDATE-STRESS.md).
Everything recomputed here from the literal strings, mpmath dps=90.
No import of lead helpers.
"""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 90
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAL = ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json"
J = json.loads(CAL.read_text(encoding="utf-8"))

Ffun = lambda a, t, r, w: t * t - 2 * t * r - a * t + a * r + a * a
def Gfun(a, t, r, w):
    b = (1 + a + r) / 2
    return (1 + t * t - r * r) * (3 * b * b + w * w) - t * (3 * b * b - w * w + 6 * b * w)
def Hfun(a, t, r, w):
    return 4 * w * w - 12 * r * r + 3 * (1 - a - r) ** 2
def Tfun(a, t, r, w):
    b = (1 + a + r) / 2
    S = b * b + w * w / 3
    A = 3 * b * b - w * w - 2 * b * w
    return w * S * S * (2 * a - t + r) * (1 - t * t - r * r) + (S - b) * (2 * t - 2 * r - a) * t * t * A

vals = [mp.mpf(s) for s in J["root"]]
a, t, r, w = vals
print("root (as parsed, dps=90):")
for nm, v in zip("a t r w".split(), vals):
    print(f"  {nm} = {mp.nstr(v, 70)}")
print("\nrecorded residuals:", J["residual"])
print("my F,G,H residuals:")
for nm, v in (("F", Ffun(a, t, r, w)), ("G", Gfun(a, t, r, w)), ("H", Hfun(a, t, r, w))):
    print(f"  {nm} = {mp.nstr(v, 8)}")
TV = Tfun(a, t, r, w)
print(f"  T = {mp.nstr(TV, 20)}   (|T| = {mp.nstr(abs(TV), 8)})")

# geometry quantities and derived weights at the recorded root
b = (1 + a + r) / 2
S = b * b + w * w / 3
A = 3 * b * b - w * w - 2 * b * w
q = 2 * (1 - b) / r
u = q * r / (2 * a - t + r)
x = -b * r * r / (S - b)
y = (b - 1) * S / (S - b)
j = u * (2 * t - 2 * r - a) / r
z = j * r * t / (1 - t * t - r * r)
p = mp.mpf(1)
tot = 6 * x + 6 * y + 6 * z + 6 * p + 3 * q + 6 * u + 3 * j
print("\nderived quantities:")
print(f"  b = {mp.nstr(b,30)}  S=s^2 = {mp.nstr(S,30)}  S-b = {mp.nstr(S-b,20)}")
print(f"  A = {mp.nstr(A,20)}  beta = {mp.nstr(mp.atan2(w/mp.sqrt(3), b),20)}")
print(f"  weights x,y,z,p,q,u,j = {[mp.nstr(v,18) for v in (x,y,z,p,q,u,j)]}")
print(f"  total W = {mp.nstr(tot,20)}")
print("\nother relations:")
print(f"  a+r-1            = {mp.nstr(a+r-1,10)}")
print(f"  d+r^2 - S        = {mp.nstr(a+r+r*r-S,10)}")   # d + r^2 should equal S
print(f"  2a-t+r           = {mp.nstr(2*a-t+r,10)}")
print(f"  2t-2r-a          = {mp.nstr(2*t-2*r-a,10)}")
print(f"  1-t^2-r^2        = {mp.nstr(1-t*t-r*r,10)}")
print(f"  (1+t^2-r^2)/(2t) = {mp.nstr((1+t*t-r*r)/(2*t),20)}")
print(f"  cos(pi/3-2beta)  = {mp.nstr(mp.cos(mp.pi/3-2*mp.atan2(w/mp.sqrt(3),b)),20)}")
print(f"  A/(2*sqrt3*S)    = {mp.nstr(A/(2*mp.sqrt(3)*S),20)}")
print(f"  y*v - z*t*sin(alpha) = {mp.nstr(y*(w/mp.sqrt(3)) - z*t*(A/(2*mp.sqrt(3)*S)),15)}")
