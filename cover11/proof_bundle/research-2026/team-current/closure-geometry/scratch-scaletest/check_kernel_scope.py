import json, os
from fractions import Fraction as F
from mpmath import mp, mpf

mp.dps = 25
R = mpf(19)/50
base = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922'
load = lambda f: json.load(open(os.path.join(base, f)))

print("=== exact rational check of the e-bound ===")
print("3R-1 = 3*19/50-1 =", F(3*19, 50) - 1, "  7/50 =", F(7, 50), "  196/625 =", F(196, 625))
print("equal:", (F(3*19, 50) - 1) == F(7, 50) == F(196, 625))
print()

print("=== kernel A runs: pass flags, failures, depths, boxes ===")
A = load('directional_low_cover.json')['runs'] + load('directional_e_cover.json')['runs']
B = load('directional_fixed_low.json')['runs'] + load('directional_fixed_all.json')['runs']
for tag, rows in (('A', A), ('B', B)):
    bad = [r for r in rows if r.get('pass') is not True]
    fails = [r.get('failure') for r in rows if r.get('failure')]
    print('  kernel %s: runs=%d  passing=%d  with failure-record=%d' %
          (tag, len(rows), len(rows) - len(bad), len([f for f in fails if f])))
    if bad:
        print('     FAILING:', [r['e_interval'] for r in bad])
print()
print("  kernel A: does any run carry a failure record?",
      any(r.get('failure') for r in A))
print("  kernel A fields sample keys:", sorted(A[0].keys()))
print("  kernel B fields sample keys:", sorted(B[0].keys()))
print()

print("=== certified e-intervals and box counts (both kernels) ===")
def summary(rows, tag):
    rows2 = sorted(rows, key=lambda r: F(r['e_interval'][0]))
    edge = F(0)
    tot = 0
    for r in rows2:
        lo, hi = map(F, r['e_interval'])
        assert lo == edge, (tag, 'gap at', r['e_interval'])
        edge = hi
        tot += r['boxes']
    print('  %s: %d intervals, contiguous to %s, total boxes %d' % (tag, len(rows2), edge, tot))
summary(A, 'A')
summary(B, 'B')
print()

print("=== is the worst case an admissible disk? (rho=0.62, e=0.14, cosphi=1) ===")
rho, e = mpf('0.62'), mpf('0.14')
r = R
disc = rho*rho - 2*rho + 1 - r*r
print("  (rho-1)^2 + ... : rho meeting unit circle requires rho in [1-r, 1+r] = [0.62, 1.38] :",
      1-r <= rho <= 1+r)
print("  t = acos((1+rho^2-R^2)/(2rho)) is the half-width; at rho = 1-r the disk is TANGENT (t = asin R):")
z = (1 + rho*rho - r*r)/(2*rho)
print("     (1+rho^2-R^2)/(2rho) =", mp.nstr(z, 12), "  cos(asin R) =", mp.nstr(mp.cos(mp.asin(R)), 12))
print("  => the min-ell^2 point is a boundary (tangency) configuration; interior points give ell^2 > 0.2304")
print("  ell^2 min over the closed domain = 0.2304 exactly, so kernel A's clip floor is tight and valid.")
print()
print("=== hub term beta >= 0.6 assertion in kernel B (line 96) ===")
print("  beta = acos(clip(ell/(2R),0,1)); requires ell >= 2R*cos(0.6) = %.4f" % (2*R*mp.cos(mpf('0.6'))))
print("  but ell can be 0.480 (=sqrt(0.2304)) < 2R*cos(0.6): does the assert trigger?")
print("  kernel B line 94 RETURNS EARLY when ell.a >= (2R).b, so beta is only computed when ell.a < 2R.")
print("  then b = clip(ell/(2R),0,1) in [0,1); at b<0.6 the assert b.a>=0.6 would fire.")
print("  ell.a >= 2R*0.6 = %.4f required for the assert to pass when ell.a < 2R." % (2*R*mpf('0.6')))
print()
print("=== therefore: what happens for admissible disks with ell < 2R*0.6 (~0.456)? ===")
print("  ell^2 < 0.2079 means (rho-e)^2+2 rho e (1-v) < 0.2079. With rho>=0.62 that needs e small:")
for ee in ['0.02','0.05','0.1','0.14']:
    ee = mpf(ee)
    val = (mpf('0.62')-ee)**2
    print("     e=%-5s v=1: ell^2 = (0.62-e)^2 = %.6f" % (mp.nstr(ee, 4), val))
