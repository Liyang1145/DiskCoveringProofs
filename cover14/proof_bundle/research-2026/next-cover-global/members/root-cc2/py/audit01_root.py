"""root-cc2 audit step 1 (NUMERIC ONLY, no certificate):
independent recomputation of the D2-family geometry, the two contact equations F,G,
and the stationarity combination used by lead/root_scout.py.

Read-only inputs:
  lead/root-scout.json          (the new root, as decimal strings)
  lead/root_scout.py            (definitions to be audited)
  root_scout inputs: research-2026/session2/type14/out/hprec_sol.json (old point)

Nothing here is a proof.  It is the numeric pre-check required before an
interval/Krawczyk certificate.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 90
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]                      # .../next-cover-global
WS = HERE.parents[4]                       # ai4math2
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)

scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z0, C0, r0 = [mp.mpf(s) for s in scout['z_c_r']]
hprec = json.loads((WS / 'research-2026/session2/type14/out/hprec_sol.json').read_text())

log = []
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s); log.append(s)

# ---------------------------------------------------------------- geometry
def geom(z, c, r):
    """lead's geometry.  NOTE: lead's script uses the name `a` for A and `dd` for D."""
    s = mp.sqrt(1 - r*r)                      # U
    A = (s + z) / 2
    t = r + mp.sqrt(r*r - z*z)                # site3 = (0,t)
    B = r + mp.sqrt(r*r - (A - z)**2)         # site1 = (A,B)
    D = 1 - mp.sqrt(r*r - c*c)                # site2 = (c,D)
    return dict(s=s, A=A, B=B, c=c, D=D, t=t, z=z, r=r)

def fg(z, c, r):
    g = geom(z, c, r)
    A, B, C, D, t = g['A'], g['B'], g['c'], g['D'], g['t']
    v1 = (1 + A*A + B*B - r*r) / 2
    v2 = (1 + C*C + D*D - r*r) / 2
    det = A*D - B*C
    p1 = ((v1*D - v2*B)/det, (A*v2 - C*v1)/det)
    cross = (C - A)*(t - B) - (D - B)*(-A)
    l1 = (A-C)**2 + (B-D)**2
    l2 = C*C + (D-t)**2
    l3 = A*A + (B-t)**2
    F = (p1[0]*p1[0] + p1[1]*p1[1] - 1)**2 + (p1[0]-A)**2 + (p1[1]-B)**2 - r*r
    G = l1*l2*l3 - 4*r*r*cross*cross
    return F, G, g, dict(p1=p1, det=det, l1=l1, l2=l2, l3=l3, cross=cross, v1=v1, v2=v2)

def equations(z, c, r):
    fz = mp.diff(lambda zz: fg(zz, c, r)[0], z)
    gz = mp.diff(lambda zz: fg(zz, c, r)[1], z)
    fc = mp.diff(lambda cc: fg(z, cc, r)[0], c)
    gc = mp.diff(lambda cc: fg(z, cc, r)[1], c)
    F, G, _, _ = fg(z, c, r)
    return F, G, fz*gc - fc*gz, dict(fz=fz, gz=gz, fc=fc, gc=gc)

P('=' * 78)
P('A. reproduce lead/root-scout.json residuals at its own z,C,r')
F, G, H, d = equations(z0, C0, r0)
P('   F  =', mp.nstr(F, 30))
P('   G  =', mp.nstr(G, 30))
P('   FzGc-FcGz =', mp.nstr(H, 30))
P('   json residuals =', scout['residuals'])
P('   json z_c_r      =', scout['z_c_r'])
# relative error of the interior computations
P('   max |computed - json| =', mp.nstr(max(abs(F - mp.mpf(scout['residuals'][0])),
                                            abs(G - mp.mpf(scout['residuals'][1])),
                                            abs(H - mp.mpf(scout['residuals'][2]))), 6))

P('')
P('=' * 78)
P('B. geometry at the new root')
g = geom(z0, C0, r0)
for k in ('s', 'A', 'B', 'c', 'D', 't', 'z', 'r'):
    P('   %-2s = %s' % (k, mp.nstr(g[k], 34)))
P('   lead json a_b_c_d_s_z_t_r =', scout['a_b_c_d_s_z_t_r'])
P('   V = sqrt(r^2-z^2)   =', mp.nstr(mp.sqrt(r0*r0 - z0*z0), 34))
P('   r - A               =', mp.nstr(r0 - g['A'], 34))

P('')
P('=' * 78)
P('C. RADICAL BRANCH AUDIT (the point the human flagged)')
# C1: sigma_t branch: t = r + V  (V>0) vs t = r - V
V = mp.sqrt(r0*r0 - z0*z0)
P('   sqrt(r^2-z^2) = %s   (>0 : %s)' % (mp.nstr(V, 30), V > 0))
P('   t=r+V = %s ; t=r-V = %s ; lead t = %s' % (mp.nstr(r0+V, 24), mp.nstr(r0-V, 24),
                                                mp.nstr(g['t'], 24)))
# C2: sigma_B branch: B = r + sqrt(r^2-(A-z)^2) vs r - ...
rB = r0*r0 - (g['A'] - z0)**2
P('   radicand_B = r^2-(A-z)^2 = %s' % mp.nstr(rB, 30))
P('   B=r+sqrt(radicand_B) = %s ; B=r-sqrt = %s ; lead B = %s'
  % (mp.nstr(r0+mp.sqrt(rB), 24), mp.nstr(r0-mp.sqrt(rB), 24), mp.nstr(g['B'], 24)))
# C3: IDENTITY between radicands
ident = (r0*r0 - (g['A'] - z0)**2) - (r0*r0 - z0*z0)
P('   radicand_B - radicand_t = %s   (exact-arithmetic simplification)' % mp.nstr(ident, 30))
P('   symbolic check:  r^2-(A-z)^2-(r^2-z^2) with A=(U+z)/2  ->  -(U-z)(U+3z)/4')
U = g['s']
P('   -(U-z)(U+3z)/4 = %s' % mp.nstr(-(U-z0)*(U+3*z0)/4, 30))
# C4: sigma_D branch: D = 1 - sqrt(r^2-C^2)
rD = r0*r0 - C0*C0
P('   radical_D = r^2-C^2 = %s' % mp.nstr(rD, 30))
P('   D=1-sqrt(rD) = %s ; D=1+sqrt(rD) = %s ; lead D = %s'
  % (mp.nstr(1-mp.sqrt(rD), 24), mp.nstr(1+mp.sqrt(rD), 24), mp.nstr(g['D'], 24)))
# C5: sigma_s
P('   s = sqrt(1-r^2) = %s ; lead s = %s' % (mp.nstr(mp.sqrt(1-r0*r0), 24), mp.nstr(g['s'], 24)))

P('')
P('=' * 78)
P('D. GEOMETRY AUDIT: switch point p and the two contact structures')
F2, G2, _, aux = fg(z0, C0, r0)
p1 = aux['p1']
P('   p1 = (%s, %s)' % (mp.nstr(p1[0], 30), mp.nstr(p1[1], 30)))
P('   |p1|      = %s   (should be 1)' % mp.nstr(mp.sqrt(p1[0]**2 + p1[1]**2), 30))
P('   |p1-S1|   = %s   (should be r=%s)' % (mp.nstr(mp.sqrt((p1[0]-g['A'])**2 + (p1[1]-g['B'])**2), 30), mp.nstr(r0, 30)))
P('   |p1-S2|   = %s   (should be r)' % mp.nstr(mp.sqrt((p1[0]-C0)**2 + (p1[1]-g['D'])**2), 30))
P('   p1 in first quadrant?  %s' % (p1[0] > 0 and p1[1] > 0))
# the OTHER intersection of the two radius-r circles (reflection through the S1S2 axis)
P('   det = A*D-B*c = %s' % mp.nstr(aux['det'], 30))
mid = ((g['A']+C0)/2, (g['B']+g['D'])/2)
u = (C0-g['A'], g['D']-g['B'])
nu = mp.sqrt(u[0]**2+u[1]**2)
h = mp.sqrt(r0*r0 - (nu/2)**2)
nperp = (-u[1]/nu, u[0]/nu)
p2 = (mid[0]+h*nperp[0], mid[1]+h*nperp[1]); p1b = (mid[0]-h*nperp[0], mid[1]-h*nperp[1])
P('   two circle-circle intersections: (%s,%s) and (%s,%s)'
  % (mp.nstr(p2[0], 24), mp.nstr(p2[1], 24), mp.nstr(p1b[0], 24), mp.nstr(p1b[1], 24)))
P('   |p2| = %s ; |p1b| = %s   (unit circle hits only if one of them = 1)'
  % (mp.nstr(mp.sqrt(p2[0]**2+p2[1]**2), 24), mp.nstr(mp.sqrt(p1b[0]**2+p1b[1]**2), 24)))
# G: circumradius
P('   l1,l2,l3 (squared sides) = %s %s %s' % (mp.nstr(aux['l1'], 24), mp.nstr(aux['l2'], 24), mp.nstr(aux['l3'], 24)))
P('   cross (signed 2*area)    = %s' % mp.nstr(aux['cross'], 24))
P('   circumradius (abc/4Area) = %s   (should be r=%s)'
  % (mp.nstr(mp.sqrt(aux['l1'])*mp.sqrt(aux['l2'])*mp.sqrt(aux['l3'])/(4*abs(aux['cross'])/2), 30), mp.nstr(r0, 30)))
P('   G/l1l2l3 = %s   (should be 0)' % mp.nstr(G2/(aux['l1']*aux['l2']*aux['l3']), 24))

P('')
P('=' * 78)
P('E. derivatives: hand-written forward dual vs mp.diff')
fz, gz, fc, gc = equations(z0, C0, r0)[3].values()
P('   Fz = %s' % mp.nstr(fz, 30))
P('   Gz = %s' % mp.nstr(gz, 30))
P('   Fc = %s' % mp.nstr(fc, 30))
P('   Gc = %s' % mp.nstr(gc, 30))
P('   Fz*Gc-Fc*Gz = %s' % mp.nstr(H, 30))
# 3x3 jacobian of Phi=(F,G,FzGc-FcGz)
def Phi(v):
    return equations(v[0], v[1], v[2])[:3]
sol = [z0, C0, r0]
J = mp.matrix(3, 3)
for j in range(3):
    for i in range(3):
        J[i, j] = mp.diff(lambda t: Phi(sol[:j] + [t] + sol[j+1:])[i], sol[j])
P('   det dPhi/d(z,c,r) = %s   (lead json: %s)'
  % (mp.nstr(mp.det(J), 30), scout['Jacobian_determinant']))
# 2x2 jacobian of (F,G) wrt (z,c)
J2 = mp.matrix([[fz, fc], [gz, gc]])
P('   det d(F,G)/d(z,c) = %s' % mp.nstr(mp.det(J2), 30))

P('')
P('=' * 78)
P('F. residuals at the OLD hprec point, same kernels (old point = (z,C,r) from hprec th)')
th = hprec['th']
P('   hprec th_names =', hprec['th_names'])
P('   hprec th       =', [mp.nstr(mp.mpf(t), 12) for t in th])
P('   hprec R        =', hprec['R'])
zo, Co, ro = mp.mpf(th[5]), mp.mpf(th[2]), mp.mpf(hprec['R'])
P('   old point used by root_scout: (z,C,r) = (th[5],th[2],R) = (%s,%s,%s)'
  % (mp.nstr(zo, 24), mp.nstr(Co, 24), mp.nstr(ro, 24)))
Fo, Go, Ho, _ = equations(zo, Co, ro)
P('   F=%s G=%s FzGc-FcGz=%s' % (mp.nstr(Fo, 20), mp.nstr(Go, 20), mp.nstr(Ho, 20)))
P('   det d(F,G)/d(z,c) at old = %s' % mp.nstr(mp.det(mp.matrix([[mp.diff(lambda t: fg(t, Co, ro)[0], zo), mp.diff(lambda t: fg(zo, t, ro)[0], Co)],
                                                                  [mp.diff(lambda t: fg(t, Co, ro)[1], zo), mp.diff(lambda t: fg(zo, t, ro)[1], Co)]])), 20))

(OUT / 'audit01_root.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'audit01_root.txt')
