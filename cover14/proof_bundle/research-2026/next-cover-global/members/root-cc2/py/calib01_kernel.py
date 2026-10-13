"""root-cc2 CALIBRATION (ASCII only, final kernel): does the interval kernel compute
the intended quantity?

Checks, at and around the lead root (z0,C0,r0) from lead/root-scout.json:
  (0) two textbook functions with independently hand-computed values / mixed 2nd derivs
  (1) point evaluation of Phi = (F,G,J) vs an mpmath .diff reference kernel
  (2) gradients dF, dG vs mp.diff
  (3) Hessians of F, G and (J, grad J) vs EXACT symbolic (sympy) derivatives
  (4) interval containment on a box: the enclosure contains the point values at 343
      interior samples (endpoint-bug detector; sampling is NOT a proof)
  (5) finite-difference check of the Jacobian enclosure on a small box
Nothing here is a certificate; the certificate is cert01_krawczyk.py.
"""
import json
import sys
from pathlib import Path
import mpmath as mp
from mpmath import iv
import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ivkernel as K

mp.mp.dps = 60
iv.dps = 60
NCG = HERE.parents[2]
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z0, C0, r0 = [mp.mpf(s) for s in scout['z_c_r']]

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

def M(x):
    return (mp.mpf(x.a.a) + mp.mpf(x.b.b)) / 2

def NUM(x, n=24):
    return mp.nstr(M(x), n)

# ---------------------------------------------------------------- reference kernel
def fg_ref(z, c, r):
    s = mp.sqrt(1 - r*r); A = (s + z)/2
    t = r + mp.sqrt(r*r - z*z)
    B = r + mp.sqrt(r*r - (A - z)**2)
    D = 1 - mp.sqrt(r*r - c*c)
    v1 = (1 + A*A + B*B - r*r)/2; v2 = (1 + c*c + D*D - r*r)/2
    det = A*D - B*c
    p1 = ((v1*D - v2*B)/det, (A*v2 - c*v1)/det)
    cross = (c - A)*(t - B) - (D - B)*(-A)
    l1 = (A-c)**2 + (B-D)**2; l2 = c*c + (D-t)**2; l3 = A*A + (B-t)**2
    F = (p1[0]**2 + p1[1]**2 - 1)**2 + (p1[0]-A)**2 + (p1[1]-B)**2 - r*r
    G = l1*l2*l3 - 4*r*r*cross*cross
    return F, G

def phi_ref(z, c, r):
    F, G = fg_ref(z, c, r)
    Fz = mp.diff(lambda u: fg_ref(u, c, r)[0], z); Gz = mp.diff(lambda u: fg_ref(u, c, r)[1], z)
    Fc = mp.diff(lambda u: fg_ref(z, u, r)[0], c); Gc = mp.diff(lambda u: fg_ref(z, u, r)[1], c)
    return [F, G, Fz*Gc - Fc*Gz]

lbl = ['z', 'C', 'r']

P('=' * 78)
P('(0) textbook functions (hand values, independent of the kernel)')
x = K.Hyper.dvar(K.iv_thin(3)); y = K.Hyper.evar(K.iv_thin(4))
f1 = x*x*y.sqrt()
u = K.Hyper.dvar(K.iv_thin(2)); v = K.Hyper.evar(K.iv_thin(5))
f2 = (u*v).inv()
tol = mp.mpf('1e-35')
for nm, obj, val, r4 in (('x^2*sqrt(y) @ (3,4)', f1, 18, mp.mpf(3)/2),
                         ('1/(x*y) @ (2,5)', f2, mp.mpf(1)/10, mp.mpf(1)/100)):
    ok = abs(M(obj.v) - val) <= tol and abs(M(obj.r4) - r4) <= tol
    P('   %-30s %s   value=%s (exp %s)  mixed-second=%s (exp %s)'
      % (nm, 'OK' if ok else 'FAIL', NUM(obj.v), val, NUM(obj.r4), r4))

P('')
P('=' * 78)
P('(1) point Phi: kernel vs reference (mp.diff)')
pt = K.phi_intervals(K.iv_thin(z0), K.iv_thin(C0), K.iv_thin(r0))
ref = phi_ref(z0, C0, r0)
for name, aa, bb in zip(('F', 'G', 'J'), pt, ref):
    P('   %s  kernel=%-30s ref=%-30s |diff|=%.3g' % (name, NUM(aa), mp.nstr(bb, 24), abs(M(aa) - bb)))

P('')
P('=' * 78)
P('(2) gradients dF, dG: kernel vs mp.diff')
Jm = K.jacobian_intervals(K.iv_thin(z0), K.iv_thin(C0), K.iv_thin(r0))
def pt_diff(f, xx, i):
    return mp.diff(lambda t: f(xx[:i] + [t] + xx[i+1:]), xx[i])
for row, fi, nm in ((0, 0, 'F'), (1, 1, 'G')):
    for k in range(3):
        jv = M(Jm[row][k])
        rv = pt_diff(lambda t: fg_ref(*t)[fi], [z0, C0, r0], k)
        P('   %s_%s kernel=%-24s ref=%-24s |diff|=%.3g'
          % (nm, lbl[k], mp.nstr(jv, 22), mp.nstr(rv, 22), abs(jv - rv)))

P('')
P('=' * 78)
P('(3) Hessians of F,G and (J, grad J) vs EXACT symbolic derivatives (sympy)')
zs, Cs, rs = sp.symbols('z C r', positive=True)
S = sp.sqrt(1 - rs**2)
A = (S + zs)/2
T = rs + sp.sqrt(rs**2 - zs**2)
B = rs + sp.sqrt(rs**2 - (A - zs)**2)
D = 1 - sp.sqrt(rs**2 - Cs**2)
v1 = (1 + A**2 + B**2 - rs**2)/2
v2 = (1 + Cs**2 + D**2 - rs**2)/2
det = A*D - B*Cs
p1x = (v1*D - v2*B)/det
p1y = (A*v2 - Cs*v1)/det
Fex = (p1x**2 + p1y**2 - 1)**2 + (p1x - A)**2 + (p1y - B)**2 - rs**2
crossex = (Cs - A)*(T - B) - (D - B)*(-A)
l1 = (A - Cs)**2 + (B - D)**2
l2 = Cs**2 + (D - T)**2
l3 = A**2 + (B - T)**2
Gex = l1*l2*l3 - 4*rs**2*crossex**2
Jex = sp.diff(Fex, zs)*sp.diff(Gex, Cs) - sp.diff(Fex, Cs)*sp.diff(Gex, zs)
subs = {zs: sp.Rational(str(mp.nstr(z0, 55))), Cs: sp.Rational(str(mp.nstr(C0, 55))),
        rs: sp.Rational(str(mp.nstr(r0, 55)))}
vars3 = [zs, Cs, rs]

Hk = K._second_derivatives([K.iv_thin(z0), K.iv_thin(C0), K.iv_thin(r0)])
maxerr = mp.mpf(0)
for t, e, nm in ((0, Fex, 'F'), (1, Gex, 'G')):
    for i in range(3):
        for k in range(3):
            val = mp.mpf(str(sp.N(sp.diff(e, vars3[i], vars3[k]).subs(subs), 50)))
            err = abs(val - M(Hk[t][i][k]))
            maxerr = max(maxerr, err)
            if err > mp.mpf('1e-20'):
                P('   MISMATCH H %s d2/d%s d%s exact=%s kernel=%s' % (nm, lbl[i], lbl[k], val, NUM(Hk[t][i][k])))
Jv = mp.mpf(str(sp.N(Jex.subs(subs), 50)))
dv = abs(M(pt[2]) - Jv)
P('   J   kernel=%-26s exact=%-26s |diff|=%.3g' % (NUM(pt[2]), mp.nstr(Jv, 24), dv))
maxerrJ = dv
for k in range(3):
    val = mp.mpf(str(sp.N(sp.diff(Jex, vars3[k]).subs(subs), 50)))
    err = abs(val - M(Jm[2][k]))
    maxerrJ = max(maxerrJ, err)
    if err > mp.mpf('1e-20'):
        P('   MISMATCH dJ/d%s exact=%s kernel=%s' % (lbl[k], val, NUM(Jm[2][k])))
P('   max |kernel Hessian(F,G) - exact|  = %.3g   (18 entries)' % float(maxerr))
P('   max |kernel (J, grad J) - exact|   = %.3g   (4 values)' % float(maxerrJ))

P('')
P('=' * 78)
P('(4) interval containment on the certificate box (endpoint-bug detector)')
zlo, zhi = mp.mpf('0.32681'), mp.mpf('0.32682')
Clo, Chi = mp.mpf('0.29194'), mp.mpf('0.29195')
rlo, rhi = mp.mpf('0.33173'), mp.mpf('0.33174')
env = K.phi_intervals(K.iv_from(zlo, zhi), K.iv_from(Clo, Chi), K.iv_from(rlo, rhi))
fails = 0
N = 6
for i in range(N+1):
    for j in range(N+1):
        for k in range(N+1):
            zz = zlo + (zhi-zlo)*mp.mpf(i)/N
            cc = Clo + (Chi-Clo)*mp.mpf(j)/N
            rr = rlo + (rhi-rlo)*mp.mpf(k)/N
            vv = phi_ref(zz, cc, rr)
            for q in range(3):
                if not (K.L(env[q]) <= vv[q] <= K.R(env[q])):
                    fails += 1
                    if fails < 6:
                        P('   CONTAINMENT FAILURE q=%d (%.5f,%.5f,%.5f) val=%s env=[%s,%s]'
                          % (q, zz, cc, rr, mp.nstr(vv[q], 12),
                             mp.nstr(K.L(env[q]), 12), mp.nstr(K.R(env[q]), 12)))
for q, nm in enumerate('FGJ'):
    P('   enclosure Phi[%s] = [%s, %s]  width=%s'
      % (nm, mp.nstr(K.L(env[q]), 18), mp.nstr(K.R(env[q]), 18), mp.nstr(K.wid(env[q]), 6)))
P('   containment failures over %d interior samples: %d' % ((N+1)**3, fails))

P('')
P('=' * 78)
P('(5) Jacobian enclosure vs central differences on a small box')
dz = mp.mpf('2e-6')
jb = (mp.mpf('0.326818068949914'), mp.mpf('0.29194111896494'), mp.mpf('0.331732034276234'))
Jbox = K.jacobian_intervals(K.iv_from(jb[0]-dz, jb[0]+dz), K.iv_from(jb[1]-dz, jb[1]+dz),
                            K.iv_from(jb[2]-dz, jb[2]+dz))
bad = 0
for i in range(3):
    for rr in range(3):
        pp = list(jb); pp[i] = jb[i] + dz
        pm = list(jb); pm[i] = jb[i] - dz
        fd = (K.phi_intervals(K.iv_thin(pp[0]), K.iv_thin(pp[1]), K.iv_thin(pp[2]))[rr]
              - K.phi_intervals(K.iv_thin(pm[0]), K.iv_thin(pm[1]), K.iv_thin(pm[2]))[rr]) / (2*dz)
        lo, hi = K.L(Jbox[rr][i]), K.R(Jbox[rr][i])
        if not (lo <= fd <= hi):
            bad += 1
            P('   FD outside enclosure: dPhi[%d]/d%s fd=%s env=[%s,%s]'
              % (rr, lbl[i], mp.nstr(fd, 16), mp.nstr(lo, 16), mp.nstr(hi, 16)))
P('   central differences outside the enclosure: %d of 9 (FD truncation ~%.1e)'
  % (bad, float(dz*dz)))

(HERE.parent / 'evidence' / 'calib01_kernel.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written] evidence/calib01_kernel.txt')

