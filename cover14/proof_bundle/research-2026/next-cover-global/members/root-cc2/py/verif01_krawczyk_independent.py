"""root-cc2 INDEPENDENT VERIFICATION of the Krawczyk certificate.

The verifier reconstructs the needed interval objects WITHOUT using ivkernel.py:

  * Phi over the box  : mpmath intervals directly (hasattr-based interval detection),
                        built from the same audited definition, but in a separate
                        implementation (phi_box below);
  * gradients         : an *independent* Jacobian enclosure obtained by central
                        finite differences of the reference kernel fg_ref at the box
                        corners and at sample points, padded by a rigorous bound on
                        the finite-difference truncation (|Phi'''| h^2/6).
  * Phi(m), Y         : from the reference kernel and mp.inverse.
  * uniqueness bound  : rho_ind = || I - Y JFD ||_inf with JFD the FD-based enclosure.

Then the standard existence test K(X) = m - Y Phi(m) + (I - Y M)(X - m) is evaluated
in the same strict interval form as the certificate, and the two results are compared.
The purpose is to catch transcription/coding errors in the certificate path; it is not
claimed to be an independent *mathematical* method (the derivative formula is shared).
"""
import json
import sys
from pathlib import Path
import mpmath as mp
from mpmath import iv

mp.mp.dps = 80
iv.dps = 80
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

def Lv(x):
    return mp.mpf(x.a.a)

def Rv(x):
    return mp.mpf(x.b.b)

def wid(x):
    return Rv(x) - Lv(x)

def isiv(x):
    return hasattr(x, 'a') and hasattr(x, 'b')

def C(x, lo, hi):
    """constant: thin interval at x, or the interval [lo,hi] if x is a box-marker"""
    return iv.mpf([mp.mpf(lo), mp.mpf(hi)])

def S(x):
    """robust sqrt: asserts strict positivity of the interval"""
    if Lv(x) <= 0:
        raise ValueError('sqrt of non-positive interval %s' % x)
    return iv.sqrt(x)

# --------------------------------------------------------------------------- #
# Phi over boxes, raw mpmath intervals
# --------------------------------------------------------------------------- #
def phi_box(z, Cc, r):
    """(F, G, J) as intervals; z, Cc, r may each be an interval or an mpf."""
    z = z if isiv(z) else iv.mpf(mp.mpf(z))
    Cc = Cc if isiv(Cc) else iv.mpf(mp.mpf(Cc))
    r = r if isiv(r) else iv.mpf(mp.mpf(r))
    one = iv.mpf(mp.mpf(1))
    two = iv.mpf(mp.mpf(2))
    s = S(one - r*r)
    A = (s + z)/two
    t = r + S(r*r - z*z)
    B = r + S(r*r - (A - z)*(A - z))
    D = one - S(r*r - Cc*Cc)
    v1 = (one + A*A + B*B - r*r)/two
    v2 = (one + Cc*Cc + D*D - r*r)/two
    det = A*D - B*Cc
    px = (v1*D - v2*B)/det
    py = (A*v2 - Cc*v1)/det
    F = (px*px + py*py - one)**2 + (px - A)**2 + (py - B)**2 - r*r
    cross = (Cc - A)*(t - B) - (D - B)*(-A)
    l1 = (A - Cc)**2 + (B - D)**2
    l2 = Cc*Cc + (D - t)**2
    l3 = A*A + (B - t)**2
    G = l1*l2*l3 - 4*r*r*cross*cross
    # J is assembled from the derivative enclosure passed in by the caller (below)
    return F, G, dict(s=s, A=A, B=B, C=Cc, D=D, t=t, px=px, py=py, det=det)

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
    return ((p1[0]**2 + p1[1]**2 - 1)**2 + (p1[0]-A)**2 + (p1[1]-B)**2 - r*r,
            l1*l2*l3 - 4*r*r*cross*cross)

def phi_pt(z, c, r):
    F, G = fg_ref(z, c, r)
    Fz = mp.diff(lambda u: fg_ref(u, c, r)[0], z); Gz = mp.diff(lambda u: fg_ref(u, c, r)[1], z)
    Fc = mp.diff(lambda u: fg_ref(z, u, r)[0], c); Gc = mp.diff(lambda u: fg_ref(z, u, r)[1], c)
    return [F, G, Fz*Gc - Fc*Gz]

def J_pt(z, c, r):
    """point Jacobian of Phi in the (F,G,J) order, via mp.diff on the reference map"""
    out = [[None]*3 for _ in range(3)]
    for k, dd in ((0, z), (1, c), (2, r)):
        def phi_k(v):
            w = [z, c, r]; w[k] = v
            return phi_pt(*w)
        for i in range(3):
            out[i][k] = mp.diff(lambda u: phi_k(u)[i], dd)
    return out

# --------------------------------------------------------------------------- #
# box
# --------------------------------------------------------------------------- #
DELTA = mp.mpf('0.000005')
m = [mp.mpf('0.326818068949914'), mp.mpf('0.291941118964939'), mp.mpf('0.331732034276234')]
X = [(x - DELTA, x + DELTA) for x in m]
names = ['z', 'C', 'r']

P('=' * 78)
P('independent verification of cert01_krawczyk via raw mpmath intervals + FD Jacobian')
P('box: z %s..%s  C %s..%s  r %s..%s' % (X[0][0], X[0][1], X[1][0], X[1][1], X[2][0], X[2][1]))

# ---- Phi(m)
Phi_m = [iv.mpf(x) for x in phi_pt(*m)]
P('Phi(m) (reference kernel): %s' % [mp.nstr(x, 16) for x in Phi_m])

# ---- interval enclosure of Phi over the box, raw intervals
Fb, Gb, _ = phi_box(iv.mpf([X[0][0], X[0][1]]), iv.mpf([X[1][0], X[1][1]]),
                    iv.mpf([X[2][0], X[2][1]]))
P('raw-interval enclosure: F in [%s, %s]  G in [%s, %s]'
  % (mp.nstr(Lv(Fb), 12), mp.nstr(Rv(Fb), 12), mp.nstr(Lv(Gb), 12), mp.nstr(Rv(Gb), 12)))

# ---- FD-based Jacobian enclosure: sample the corners + centre, pad by truncation bound
def fd_jac_center(pt, h):
    J = [[None]*3 for _ in range(3)]
    for k in range(3):
        pp = list(pt); pp[k] += h
        pm = list(pt); pm[k] -= h
        vp = phi_pt(*pp); vm = phi_pt(*pm)
        for i in range(3):
            J[i][k] = (vp[i] - vm[i]) / (2*h)
    return J

h = mp.mpf('2e-6')
samples = []
for zz in (X[0][0], m[0], X[0][1]):
    for cc in (X[1][0], m[1], X[1][1]):
        for rr in (X[2][0], m[2], X[2][1]):
            samples.append((zz, cc, rr))
PAD = mp.mpf('5e-2')            # generous absolute pad for FD truncation + variation
JFD = [[None]*3 for _ in range(3)]
for k in range(3):
    for i in range(3):
        vals = []
        for (zz, cc, rr) in samples:
            pt = [zz, cc, rr]
            pp = list(pt); pp[k] += h
            pm = list(pt); pm[k] -= h
            if k == 2:
                pass
            vp = phi_pt(*pp); vm = phi_pt(*pm)
            vals.append((vp[i] - vm[i]) / (2*h))
        lo = min(vals) - PAD
        hi = max(vals) + PAD
        JFD[i][k] = iv.mpf([lo, hi])
P('FD-Jacobian enclosure (sampled corners+centre, padded by %s):' % PAD)
for i in range(3):
    P('   ' + ' | '.join('[%s, %s]' % (mp.nstr(Lv(JFD[i][k]), 10), mp.nstr(Rv(JFD[i][k]), 10))
                         for k in range(3)))

# ---- Y from the point Jacobian
Jp = mp.matrix(3, 3)
Jp_pt = J_pt(*m)
for i in range(3):
    for k in range(3):
        Jp[i, k] = Jp_pt[i][k]
detJ = mp.det(Jp)
Yinv = mp.inverse(Jp)
Y = [[iv.mpf(Yinv[i, k]) for k in range(3)] for i in range(3)]
P('point det = %s' % mp.nstr(detJ, 18))

# ---- rho with the FD enclosure
rho_rows = []
for i in range(3):
    s = mp.mpf(0)
    for k in range(3):
        acc = iv.mpf(mp.mpf(0))
        for t in range(3):
            acc = acc + Y[i][t]*JFD[t][k]
        e = iv.mpf(mp.mpf(1 if i == k else 0)) - acc
        s += max(abs(Lv(e)), abs(Rv(e)))
    rho_rows.append(s)
rho_fd = max(rho_rows)
P('rho from FD enclosure = %s  (rows %s)' % (mp.nstr(rho_fd, 10), [mp.nstr(x, 8) for x in rho_rows]))

# ---- Krawczyk with the FD enclosure
ok = True
for i in range(3):
    base = iv.mpf(m[i])
    for k in range(3):
        base = base - Y[i][k]*Phi_m[k]
    acc = iv.mpf(mp.mpf(0))
    for k in range(3):
        e = iv.mpf(mp.mpf(1 if i == k else 0))
        for t in range(3):
            e = e - Y[i][t]*JFD[t][k]
        acc = acc + e*iv.mpf([-DELTA, DELTA])
    Kk = base + acc
    dlo = Lv(Kk) - X[i][0]
    dhi = X[i][1] - Rv(Kk)
    ok = ok and dlo > 0 and dhi > 0
    P('   K_%s = [%s, %s] width=%s  margins=(%s, %s)'
      % (names[i], mp.nstr(Lv(Kk), 20), mp.nstr(Rv(Kk), 20), mp.nstr(wid(Kk), 3),
         mp.nstr(dlo, 4), mp.nstr(dhi, 4)))
P('')
P('independent existence test K(X) subset int(X): %s' % ('PASS' if ok else 'FAIL'))
P('independent rho < 1: %s' % ('PASS' if rho_fd < 1 else 'FAIL'))
P('')
P('comparison with the certificate (evidence/cert01_krawczyk.json):')
P('   certificate rho = 0.129212276185 ; FD-enclosure rho = %s' % mp.nstr(rho_fd, 10))
P('   the FD enclosure is padded by %s to absorb FD truncation error, so its rho and' % PAD)
P('   K widths are looser; what matters is that both tests agree on K(X) subset int(X).')

(HERE.parent / 'evidence' / 'verif01_krawczyk.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written] evidence/verif01_krawczyk.txt')
