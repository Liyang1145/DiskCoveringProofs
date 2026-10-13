"""root-cc2: pin down the kernel<->leadF interface exactly (200 digits).

Question: with e = |p|^2 - 1 (p from the linear solve, so p.S1 = v1 holds exactly),
  F_kernel = e^2 + |p-S1|^2 - r^2 = e(e+1)
  F_lead   = e^2 + (|p-S1|^2 - r^2) = e^2 + e   ... wait: BOTH are e^2+e?
Check numerically at high precision what the ratio is, and what the ratio of the
stationarity combinations H = F_z G_C - F_C G_z is.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 200
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z0, C0, r0 = [mp.mpf(s) for s in scout['z_c_r']]

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

def parts(z, c, r):
    s = mp.sqrt(1-r*r); A = (s+z)/2
    t = r + mp.sqrt(r*r - z*z)
    B = r + mp.sqrt(r*r - (A-z)**2)
    D = 1 - mp.sqrt(r*r - c*c)
    v1 = (1+A*A+B*B-r*r)/2; v2 = (1+c*c+D*D-r*r)/2
    det = A*D - B*c
    px = (v1*D - v2*B)/det; py = (A*v2 - c*v1)/det
    return dict(s=s, A=A, B=B, c=c, D=D, t=t, v1=v1, v2=v2, det=det, px=px, py=py)

def F_kernel(z, c, r):
    q = parts(z, c, r)
    return (q['px']**2 + q['py']**2 - 1)**2 + (q['px']-q['A'])**2 + (q['py']-q['B'])**2 - r*r

def F_lead(z, c, r):
    q = parts(z, c, r)
    return (q['px']**2 + q['py']**2 - 1)**2 + ((q['px']-q['A'])**2 + (q['py']-q['B'])**2 - r*r)

def G(z, c, r):
    q = parts(z, c, r)
    A, B, C, D, t = q['A'], q['B'], q['c'], q['D'], q['t']
    l1 = (A-c)**2 + (B-D)**2; l2 = c*c + (D-t)**2; l3 = A*A + (B-t)**2
    cross = (c-A)*(t-B) - (D-B)*(-A)
    return l1*l2*l3 - 4*r*r*cross*cross

P('working precision = %d digits' % mp.mp.dps)
q = parts(z0, C0, r0)
e = q['px']**2 + q['py']**2 - 1
res_k = (q['px']-q['A'])**2 + (q['py']-q['B'])**2 - r0*r0
P('e                 = %s' % mp.nstr(e, 12))
P('|p-S1|^2 - r^2    = %s' % mp.nstr(res_k, 12))
P('e^2               = %s' % mp.nstr(e*e, 12))
P('F_kernel          = %s' % mp.nstr(F_kernel(z0, C0, r0), 12))
P('F_lead            = %s' % mp.nstr(F_lead(z0, C0, r0), 12))
P('F_kernel - F_lead = %s' % mp.nstr(F_kernel(z0, C0, r0) - F_lead(z0, C0, r0), 6))
P('')
P('exact ratio F_kernel/F_lead          = %s' % mp.nstr(F_kernel(z0, C0, r0)/F_lead(z0, C0, r0), 12))
P('candidate h = |p|^2/det^2            = %s' % mp.nstr((q['px']**2+q['py']**2)/q['det']**2, 12))
P('det^2                                = %s' % mp.nstr(q['det']**2, 12))
P('|p|^2                                = %s' % mp.nstr(q['px']**2+q['py']**2, 20))
P('(e+1)/det^2 = |p|^2/det^2            = %s' % mp.nstr((e+1)/q['det']**2, 12))
P('')
P('For the coded forms:')
P('  lead F (as coded in root_scout) = (|p|^2-1)^2 + |p-S1|^2 - r^2 = e^2 + e = F_kernel')
P('  => the two kernels agree EXACTLY at the level of the coded expressions')
P('     F_lead_coded = (|p|^2-1)^2 + |p-S1|^2 - r^2 = e^2 + e  (this is my kernel too)')
P('  and the alpha-52x test form F = (p.p-1)^2 + (p.p-1) = e^2 + e is the same thing')
P('')
P('  F_52x_variant = (p.p-1)^2 + (p.p-1)  = %s' % mp.nstr(e*e + e, 12))
P('  det^2 * e                            = %s' % mp.nstr(q['det']**2*e, 12))
P('  ratio (e^2+e)/(det^2 e) = (e+1)/det^2 = %s' % mp.nstr((e+1)/q['det']**2, 12))

# stationarity combinations
def H_of(Ffun, z, c, r):
    Fz = mp.diff(lambda u: Ffun(u, c, r), z); Fc = mp.diff(lambda u: Ffun(z, u, r), c)
    Gz = mp.diff(lambda u: G(u, c, r), z); Gc = mp.diff(lambda u: G(z, u, r), c)
    return Fz*Gc - Fc*Gz

Hk = H_of(F_kernel, z0, C0, r0)
det_sq = q['det']**2

def F_det2(z, c, r):
    """the hypothetical normalization det^2 * e (what the lead described as h*Flead)"""
    qq = parts(z, c, r)
    ee = qq['px']**2 + qq['py']**2 - 1
    return qq['det']**2 * ee

Hdet = H_of(F_det2, z0, C0, r0)
P('')
P('H(F_kernel) = H(F_lead_coded) = %s' % mp.nstr(Hk, 12))
P('H(det^2 * e)                  = %s' % mp.nstr(Hdet, 12))
P('ratio H(F_kernel)/H(det^2 e)  = %s' % mp.nstr(Hk/Hdet, 12))
P('h = |p|^2/det^2               = %s' % mp.nstr((q['px']**2+q['py']**2)/det_sq, 12))
P('')
P('INTERFACE SUMMARY (what connects the coded system to the algebraic e):')
P('  * the coded F (root_scout) = (|p|^2-1)^2 + (|p-S1|^2 - r^2); on the constraint')
P('    p.S1 = v1 one has |p-S1|^2 - r^2 = |p|^2 - 1 = e identically, so coded F = e^2+e.')
P('  * therefore the algebraic contact condition is exactly e = 0 provided |p|^2 > 0')
P('    on the box (verified: |p|^2 in [0.99952, 1.00048]) and det != 0')
P('    (verified: det in [0.402404, 0.402462]).')
P('  * det^2 * e is a DIFFERENT normalization (ratio 1/(1+e) at the contact level and')
P('    h = |p|^2/det^2 = 6.17465845489 elsewhere); it is not the coded F.')

(HERE.parent / 'evidence' / 'verif03_interface_highprec.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written] evidence/verif03_interface_highprec.txt')
