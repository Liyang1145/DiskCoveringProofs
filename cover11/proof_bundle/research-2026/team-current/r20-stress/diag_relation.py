"""Exact relation between the TC contact functions and the site-face branch functions.

Geometry (local, at a genuine configuration):
  chord C_kC_{k+1} of length c; U = inner intersection of the two R-circles; B = outer one;
  H = hub.  With h = signed height of H over the chord line (positive on the U side),
  o = circumcenter height, rho = circumradius:
      rho^2 = c^2/4 + o^2 ,        |H-U|^2 - R^2 = 2h(o-u) ,    u = sqrt(R^2 - c^2/4)
      rho^2 - R^2   = (o-u)(o+u)
  => at the common zero (o=u) :   dF = (h/u) dG ,  F = |H-U|^2-R^2 , G = rho^2-R^2
  => d( |H-U| - R ) = (h/u) d( rho - R )      in EVERY chart direction.

This script tests that identity and the model branch identity  exp(b_face) = circumradius,
as functions along the TC chart (60-digit FD), i.e. which object is the "same object".
"""
import os, sys
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp
W = Path(__file__).parent
sys.path.insert(0, str(W))
SRC = (W / 'phase5c_scale_audit.py').read_text(encoding='utf-8')
pre = SRC.split('# ---------------------------------------------------------------- high precision chart Jacobians')[0]
NS = {'__name__': '__main__', '__file__': str(W / 'phase5c_scale_audit.py')}
exec(compile(pre, str(W / 'phase5c_scale_audit.py'), 'exec'), NS)
u0, tc_geo, at, res5, faces, model_quant = NS['u0'], NS['tc_geo'], NS['at'], NS['res5'], NS['faces'], NS['model_quant']
mp = NS['mp']; mp.mp.dps = 60
dist = lambda p, q: mp.sqrt((p[0]-q[0])**2 + (p[1]-q[1])**2)

ms = lambda k: (6 - k) % 9


def geom_contact(u, kind, k, l=0):
    """returns dict with c, uu(height of U), h(signed height of H), F, G, rho, f, and the model face index"""
    g = tc_geo(u)
    R = g['R']
    if kind == 'fan':
        P, Q, H = g['C'][k], g['C'][(k + 1) % 9], g['hubs'][l]
        U = g['U'][k]
        f_face = None
        for i, f in enumerate(faces):
            if set(f) == {ms(k), ms((k + 1) % 9), 9 + l}:
                f_face = i
    else:                                    # central: chord = H0H1, point = C_6
        P, Q, H = g['hubs'][0], g['hubs'][1], g['C'][6]
        U = g['waist']
        f_face = None
        for i, f in enumerate(faces):
            if set(f) == {9, 10, ms(6)}:
                f_face = i
    c = dist(P, Q)
    uu = mp.sqrt(R * R - c * c / 4)
    # signed height of H over the line PQ, positive on the U side
    e1 = ((Q[0] - P[0]) / c, (Q[1] - P[1]) / c)
    e2 = (-e1[1], e1[0])
    hh = (H[0] - P[0]) * e2[0] + (H[1] - P[1]) * e2[1]
    uu_s = (U[0] - P[0]) * e2[0] + (U[1] - P[1]) * e2[1]
    if hh < 0:
        hh = -hh
    # circumradius of (P,Q,H)
    la, lb, lc = dist(Q, H), dist(P, H), c
    s = (la + lb + lc) / 2
    area = mp.sqrt(s * (s - la) * (s - lb) * (s - lc))
    rho = la * lb * lc / (4 * area)
    F = dist(H, U) ** 2 - R * R
    G = rho * rho - R * R
    return dict(c=c, uu=uu, uu_s=uu_s, h=hh, rho=rho, F=F, G=G, f=dist(H, U) - R, R=R, face=f_face)


h6 = mp.mpf('1e-16')
def du(fun, k, h=h6):
    up = list(u0); um = list(u0); up[k] = up[k] + h; um[k] = um[k] - h
    return (fun(up) - fun(um)) / (2 * h)

for kind, k, l in [('fan', 1, 1), ('fan', 2, 0), ('fan', 3, 0), ('fan', 8, 1), ('central', 6, 0)]:
    g0 = geom_contact(u0, kind, k, l)
    print('== contact %s k=%d l=%d  (model face %s)' % (kind, k, l, g0['face']))
    print('   c = %.10f  u = sqrt(R^2-c^2/4) = %.10f  |U-U|=%.1e  h = %.10f  rho = %.14f  R = %.14f  rho-R = %+.2e'
          % (g0['c'], g0['uu'], g0['uu_s'] - g0['uu'], g0['h'], g0['rho'], g0['R'], g0['rho'] - g0['R']))
    print('   F = %+.2e  G = %+.2e   ratio F/G = %s' % (g0['F'], g0['G'], mp.nstr(g0['F'] / g0['G'], 6) if g0['G'] != 0 else 'n/a'))
    # model branch value at the same face
    Q = at(u0)
    print('   model exp(b_face) - rho = %+.2e   (same object check)' % (mp.e ** Q['b'][g0['face']] - g0['rho']))
    print('   dir        dF                       dG                  dF/dG        (h/u)^-1       df/dg')
    for j in range(7):
        dF = du(lambda u: geom_contact(u, kind, k, l)['F'], j)
        dG = du(lambda u: geom_contact(u, kind, k, l)['G'], j)
        df = du(lambda u: geom_contact(u, kind, k, l)['f'], j)
        dg = du(lambda u: geom_contact(u, kind, k, l)['rho'], j)      # d rho (R is a chart coord!)
        dR = du(lambda u: geom_contact(u, kind, k, l)['R'], j)
        dgg = dg - dR                                                 # d(rho - R)
        ratio = dF / dG if abs(dG) > 1e-30 else mp.mpf('nan')
        dfdg = df / dgg if abs(dgg) > 1e-30 else mp.mpf('nan')
        print('   %d   %+.8e   %+.8e   %+.8f   %+.8f   %+.8f'
              % (j, dF, dG, ratio, g0['h'] / g0['uu'], dfdg))
    print()
