"""Verify the geometric facts consumed by the k10 chain and the lead's unification."""
from fractions import Fraction as F
from mpmath import mp, mpf, asin, sqrt, acos, pi, cos, sin
mp.dps=40
r=mpf("0.33173203427623414")
s=sqrt(1-r*r)
L=2*asin(r)
print("r        ", r)
print("s=sqrt(1-r^2)=", s, "  asin(r)=", asin(r), "  2asin(r)=", L)

# (A) lemma: for centre at outer root rho+, moving to inner root rho- preserves D-intersection
print("\n(A) inner-root dominance test")
import random
random.seed(1)
worst=mpf(-1)
for trial in range(4000):
    alpha=mpf(random.random())*asin(r)
    # rho+ = cos a + sqrt(r^2-sin^2 a), rho- = cos a - sqrt(...)
    disc=r*r-sin(alpha)**2
    disc=max(disc,mpf(0))
    rp=cos(alpha)+sqrt(disc); rm=cos(alpha)-sqrt(disc)
    if rp<1: continue
    u=(1,0)
    # sample x in D cap B(rp u, r) -- construct directly
    for _ in range(20):
        th=mpf(random.random())*2*pi
        rad=sqrt(mpf(random.random()))
        x=(rad*cos(th), rad*sin(th))
        d_old=sqrt((x[0]-rp)**2+x[1]**2)
        if d_old<=r:
            d_new=sqrt((x[0]-rm)**2+x[1]**2)
            worst=max(worst,d_new-r)
    # also test the exact worst point: on the circle at the arc endpoint
    for aa in (alpha, -alpha, mpf(0)):
        x=(cos(aa),sin(aa))
        if sqrt((x[0]-rp)**2+x[1]**2)<=r:
            worst=max(worst, sqrt((x[0]-rm)**2+x[1]**2)-r)
print("   max over sampled x of (|x-inner|-r) =", worst, "  <=0 means lemma holds on sample")
# exact worst-case analytic check: x = (1,0) direction case2 endpoint
print("   check |x-rm u|^2<=r^2 at x=u: ", (1-rm)**2-r*r, " (<=0?)")
print("   rho-*rho+ - (1-r^2) =", )

# (B) constants chain pi <= asin(2rho)+7asin(rho) for rho<1/3
print("\n(B) no-chord constant chain")
for rho in [r, r+mpf('1e-6'), r+mpf('1e-3'), mpf(1)/3-mpf('1e-9')]:
    val=asin(2*rho)+7*asin(rho)
    print("   rho=%.12f  asin(2rho)+7asin(rho)=%.12f  pi=%.12f  margin=%+.3e"%(rho,val,pi,pi-val))

# (C) outward clipping: norm guard at rho=r_e/R_e for small eps
print("\n(C) outward clipping guard")
for eps in [mpf('1e-3'), mpf('1e-4'), mpf('1e-5')]:
    Re=1+eps; re=r+eps; rho=re/Re
    print("   eps=%.0e rho=%.15f  <1/3? %s ; owner halfwidth cap asin(rho)=%.12f"%(eps,rho,rho<mpf(1)/3,asin(rho)))
    # guard: site norms <= s/Re vs sqrt(1-rho^2)
    print("      s/Re=%.15f  sqrt(1-rho^2)=%.15f  guard=%+.3e"%(s/Re,sqrt(1-rho*rho),sqrt(1-rho*rho)-s/Re))
