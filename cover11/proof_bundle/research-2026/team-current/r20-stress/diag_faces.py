"""Quick diagnostic: identify each site-face branch with its geometric triangle / circumradius,
and find which face gradient each TC contact gradient is parallel to."""
import os, sys, json
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

W = Path(__file__).parent; OUT = W / 'out'
sys.path.insert(0, str(W))
SRC = (W / 'phase5c_scale_audit.py').read_text(encoding='utf-8')
pre = SRC.split('# ---------------------------------------------------------------- high precision chart Jacobians')[0]
NS = {'__name__': '__main__', '__file__': str(W / 'phase5c_scale_audit.py')}
exec(compile(pre, str(W / 'phase5c_scale_audit.py'), 'exec'), NS)
faces, u0, tc_geo, angle_vector, model_quant, at, res5 = NS['faces'], NS['u0'], NS['tc_geo'], NS['angle_vector'], NS['model_quant'], NS['at'], NS['res5']
mp = NS['mp']
mp.mp.dps = 60

Q0 = at(u0); geo = tc_geo(u0)
ms = lambda k: (6 - k) % 9
pts = {ms(k): geo['C'][k] for k in range(9)}
pts[9], pts[10] = geo['hubs'][0], geo['hubs'][1]
print('face   vertices(model labels)      exp(b_f)        circumradius      diff')
rows = []
for t, f in enumerate(faces):
    P = [pts[v] for v in f]
    a, b, c = P
    def dist(p, q): return mp.sqrt((p[0]-q[0])**2 + (p[1]-q[1])**2)
    la, lb, lc = dist(b, c), dist(a, c), dist(a, b)
    s = (la + lb + lc) / 2
    area = mp.sqrt(s * (s-la) * (s-lb) * (s-lc))
    circ = la * lb * lc / (4 * area)
    eb = mp.e ** Q0['b'][t]
    rows.append((t, f, eb, circ))
    print('%2d     %-22s  %.10f   %.10f   %+.2e' % (t, str(sorted(f)), eb, circ, eb - circ))
print()
print('20 branch values exp(b_f) (f=0..19) and R =', mp.nstr(geo['R'], 12))
print('  ', [mp.nstr(mp.e ** Q0['b'][t], 8) for t in range(20)])

# geometric radii of the triangles by TC labels
print()
print('TC junction k: |U_k - H_l| - R for l=0,1 ; also |U_k - B_k| - R (the other circle branch)')
def dist(p, q): return mp.sqrt((p[0]-q[0])**2 + (p[1]-q[1])**2)
for k in range(9):
    d0 = dist(geo['U'][k], geo['hubs'][0]) - geo['R']
    d1 = dist(geo['U'][k], geo['hubs'][1]) - geo['R']
    db = dist(geo['U'][k], geo['Bp'][k]) - geo['R']
    print('   k=%d  U_k-H0-R = %+.6e   U_k-H1-R = %+.6e   (|U_k-B_k|-R = %+.3f)' % (k, d0, d1, db))

# gradient-level matching: which face gradient is parallel to each contact gradient?
h6 = mp.mpf('1e-16')
def du(fun, k, h=h6):
    up = list(u0); um = list(u0); up[k] = up[k] + h; um[k] = um[k] - h
    return (fun(up) - fun(um)) / (2 * h)
ORDER = [0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
Gb = np.array([[float(du(lambda uu, f=f: at(uu)['b'][f], k)) for k in range(7)] for f in ORDER])
Gf = np.array([[float(du(lambda uu, i=i: res5(uu)[i], k)) for k in range(7)] for i in range(5)])
print()
print('contact gradient vs each active face gradient: cosine and best-fit relative residual')
for i in range(5):
    gi = Gf[i]
    best = None
    for j, f in enumerate(ORDER):
        gj = Gb[j]
        c = float(gi @ gj / (np.linalg.norm(gi) * np.linalg.norm(gj)))
        al = float(gi @ gj / (gj @ gj))
        rel = float(np.linalg.norm(gi - al * gj) / np.linalg.norm(gi))
        if best is None or rel < best[0]:
            best = (rel, f, c, al)
    rel, f, c, al = best
    alR = gi[6] / Gb[ORDER.index(f), 6]
    print('   contact %d: best match face %2d  cos=%.6f  alpha_ls=%.6f alpha_R=%.6f  rel_res=%.3e'
          % (i, f, c, al, alR, rel))
    print('      contact grad =', np.array2string(gi, precision=4, max_line_width=200))
    print('      face  grad  =', np.array2string(Gb[ORDER.index(f)], precision=4, max_line_width=200))
