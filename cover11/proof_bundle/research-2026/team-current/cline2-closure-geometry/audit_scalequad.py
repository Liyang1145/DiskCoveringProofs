from mpmath import mp, sin, cos, tan, atan, asin, sqrt, exp, pi, mpf, cosh
mp.dps = 30
R0 = mpf(19)/50
tmin = mpf(75)/76          # r/R0 lower bound of interest

print("=== A. Lower-allowance condition (lead's derivation) ===")
print("L condition from geometry: sin(alpha-w/2) >= rho^2 sin(w/2),  rho = r/R0")
print("with sin(w/2) = h/R0 = K s /R0 = K sqrt(x)/1 ... let us fix K = R0*sqrt(Q)/2, h = K s")

# lead's form:  A sqrt[x(1-K^2 x)] >= K (c x + tmin^2)
# We check numerically that this reproduces sin(alpha-w/2) >= tmin^2 sin(w/2)
print()
print("test: pick d, alpha, s; compute both sides of lead's inequality and of (L)")
def lead_L(d, al, x, Km=None):
    A = sin(al); c = cos(al)
    Q = 2*(cosh(2*d) - c)
    K = R0*sqrt(Q)/2
    # s = sqrt(x)
    lhs = A*sqrt(x*(1 - K*K*x))
    rhs = K*(c*x + tmin**2)
    return lhs, rhs, K

def geo_L(d, al, x):
    A = sin(al); c = cos(al)
    Q = 2*(cosh(2*d) - c)
    K = R0*sqrt(Q)/2
    s = sqrt(x); h = K*s
    w = 2*asin(h)
    return sin(al - w/2) - tmin**2*sin(w/2)

for (d, al, x) in [(mpf('0.3'), mpf('1.2'), mpf('0.5')),
                   (mpf('0.1'), mpf('1.4'), mpf('0.3')),
                   (mpf('0.5'), mpf('0.8'), mpf('0.25'))]:
    l, r, K = lead_L(d, al, x)
    g = geo_L(d, al, x)
    print("  d=%s al=%.3f x=%s: K=%.6f  lead LHS-RHS=%.3e   geo (L)=%.3e"
          % (d, al, x, K, l - r, g))

print()
print("=== B. Endpoint-max condition ===")
print("A sqrt(1-K^2 x) >= K sqrt(x)(c+E),  E=e^{2|d|}")
def lead_E(d, al, x):
    A = sin(al); c = cos(al)
    Q = 2*(cosh(2*d) - c)
    K = R0*sqrt(Q)/2
    E = exp(2*abs(d))
    return A*sqrt(1 - K*K*x) - K*sqrt(x)*(c + E), K

def geo_E(d, al, x):
    A = sin(al); c = cos(al)
    Q = 2*(cosh(2*d) - c)
    K = R0*sqrt(Q)/2
    s = sqrt(x); h = K*s
    w = 2*asin(h)
    return sin(al - w/2) - exp(2*abs(d))*sin(w/2)

print(" test on a safe point (c+E > 0):")
for (d, al, x) in [(mpf('0.3'), mpf('1.2'), mpf('0.5')),
                   (mpf('0.1'), mpf('1.4'), mpf('0.3'))]:
    l, K = lead_E(d, al, x)
    g = geo_E(d, al, x)
    print("  d=%s al=%.3f x=%s: K=%.6f lead=%.3e  geo=%.3e" % (d, al, x, K, l, g))
