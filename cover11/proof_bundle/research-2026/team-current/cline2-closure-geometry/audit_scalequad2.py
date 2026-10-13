from mpmath import mp, sin, cos, asin, sqrt, exp, pi, mpf, cosh
mp.dps = 30
R0 = mpf(19)/50

def setup(d, al, x):
    A = sin(al); c = cos(al)
    Q = 2*(cosh(2*mpf(d)) - c)
    K = R0*sqrt(Q)/2
    s = sqrt(x); h = K*s
    w = 2*asin(h)
    return A, c, Q, K, s, h, w

print("geometric (L): sin(alpha-w/2) - rho^2 sin(w/2)  [rho=1]")
print("lead L      : A sqrt(1-K^2 x) - K sqrt(x) (c + tmin^2)")
print("candidate   : A sqrt(1-K^2 x) - K sqrt(x) (c + tmin^2/x)")
print()
for (d, al, x) in [(mpf('0.3'), mpf('1.2'), mpf('0.5')),
                   (mpf('0.1'), mpf('1.4'), mpf('0.3')),
                   (mpf('0.5'), mpf('0.8'), mpf('0.25')),
                   (mpf('0.0'), mpf('1.0'), mpf('0.5'))]:
    A, c, Q, K, s, h, w = setup(d, al, x)
    geo = sin(al - w/2) - sin(w/2)
    leadL = A*sqrt(1 - K*K*x) - K*sqrt(x)*(c + mpf(75)/76**2)
    cand = A*sqrt(1 - K*K*x) - K*sqrt(x)*(c + mpf(75)/76**2/x)
    print("d=%s al=%.2f x=%s: geo=%.9f  lead=%.9f  cand=%.9f" % (d, al, x, geo, leadL, cand))

print()
print("check the ALGEBRA:  A*sqrt(1-K^2x) - K*sqrt(x)*c  =?  sin(alpha - w/2)")
print("   since sin(w/2)=K sqrt(x), cos(w/2)=sqrt(1-K^2 x):")
for (d, al, x) in [(mpf('0.3'), mpf('1.2'), mpf('0.5')), (mpf('0.1'), mpf('1.4'), mpf('0.3'))]:
    A, c, Q, K, s, h, w = setup(d, al, x)
    lhs = A*sqrt(1 - K*K*x) - K*sqrt(x)*c
    print("   d=%s al=%.2f x=%s: %.15f vs sin(alpha-w/2)=%.15f" % (d, al, x, lhs, sin(al-w/2)))

print()
print("so (L) in the lead's variables is:  A sqrt(1-K^2x) - K sqrt(x) c >= rho^2 K sqrt(x)")
print("   <=>  A sqrt(1-K^2 x) >= K sqrt(x)(c + rho^2)")
print("the lead wrote (c x + tmin^2) -- check whether that is the SQUARED form:")
print("   squaring: A^2(1-K^2x) >= K^2 x (c+rho^2)^2  ... vs lead's quadratic -K^2x^2+(A^2-2K^2 c tmin^2)x-K^2 tmin^4")
for (d, al, x) in [(mpf('0.3'), mpf('1.2'), mpf('0.5'))]:
    A, c, Q, K, s, h, w = setup(d, al, x)
    l1 = A*A*(1-K*K*x) - K*K*x*(c+mpf(75)/76**2)**2
    l2 = -K*K*x*x + (A*A - 2*K*K*c*(mpf(75)/76**2))*x - K*K*(mpf(75)/76**2)**2
    print("   squared-RHS form: %.9f ;  lead quadratic: %.9f" % (l1, l2))
