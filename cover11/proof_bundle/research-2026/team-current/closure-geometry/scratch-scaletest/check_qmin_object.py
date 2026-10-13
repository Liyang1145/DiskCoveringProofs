from mpmath import mp, sin, cos, acos, asin, sqrt, pi, mpf

mp.dps = 25
R = mpf(19)/50


def psi(d, s):
    val = (d*d + 1 - (R*s)**2)/(2*d)
    return mp.acos(val) if abs(val) <= 1 else None


print("r =", R, " sqrt(1-r^2) =", mp.nstr(sqrt(1-R*R), 15))
print("valid |c| range for the construction: [r*s, sqrt(1-r^2)]")
print()

for (d, sU, sV) in [(mpf('0.6'), mpf('0.9'), mpf('0.85')),
                    (mpf('0.7'), mpf('0.95'), mpf('0.8')),
                    (mpf('0.5'), mpf('0.99'), mpf('0.99')),
                    (mpf('0.6'), mpf('1.0'), mpf('0.75'))]:
    psU = psi(d, sU); psV = psi(d, sV)
    if psU is None or psV is None:
        print("  d=%.2f: outside the constructible range, skipped" % d); continue
    Theta = psU + psV
    cp = (d, mpf(0))
    Pu = (cos(psU), sin(psU)); Pv = (cos(-psV), sin(-psV))
    u = sqrt((Pu[0]-cp[0])**2 + (Pu[1]-cp[1])**2)/R
    v = sqrt((Pv[0]-cp[0])**2 + (Pv[1]-cp[1])**2)/R
    au = (Pu[0]-cp[0], Pu[1]-cp[1]); av = (Pv[0]-cp[0], Pv[1]-cp[1])
    cosA = (au[0]*av[0] + au[1]*av[1])/((R*u)*(R*v))
    a = mp.acos(cosA)
    q_src = (u-v)**2 + 4*u*v*sin(a/2)**2
    q_arc = 4*sin(Theta/2)**2/R**2
    print("  d=%.2f  sU=%.2f sV=%.2f" % (d, sU, sV))
    print("     Theta (arc) = %.15f   (bounded by 2 asin r = %.15f)" % (Theta, 2*asin(R)))
    print("     u=%.12f  v=%.12f  a=%.15f  (u,v <= 1: %s)" % (u, v, a, u <= 1 and v <= 1))
    print("     q_src = %.18f" % q_src)
    print("     q_arc = %.18f" % q_arc)
    print("     difference = %.3e  -> SAME OBJECT: %s" % (q_src - q_arc, abs(q_src - q_arc) < mpf('1e-18')))
    print()

print("qmin identity:  m = 2pi - 16 asin r  (per-arc lower bound);  4 sin^2(m/2)/r^2")
for r in [mpf('0.375'), mpf('0.378'), R]:
    m = 2*pi - 16*asin(r)
    q_arcform = 4*sin(m/2)**2/r**2
    q_code = 4*sin(pi - 8*asin(r))**2/r**2
    print("   r=%.5f  m/2 = %.15f  qmin = %.18f" % (r, m/2, q_arcform))
    print("        code form 4sin^2(pi-8asin r)/r^2 = %.18f   diff = %.1e" % (q_code, q_arcform-q_code))
print()
print("monotonicity of qmin in r:")
prev = None
for i in range(7):
    r = mpf('0.375') + mpf('0.0025')*i
    qm = 4*sin(pi - 8*asin(r))**2/r**2
    flag = '' if prev is None else ('DEC' if qm < prev else 'INC')
    print("   r=%.4f  qmin=%.12f  %s" % (r, qm, flag))
    prev = qm
