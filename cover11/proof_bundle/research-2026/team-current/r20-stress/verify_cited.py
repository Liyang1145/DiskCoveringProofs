"""Independent validity check of the two cleanest cited witnesses:
  W1 = phase1_runs run00 (delta=0.05, res 2.9e-13)   [non-flat by >= 2.86 deg on every sector]
  W2 = mechanism_test run06 (best maxD1, res 2.9e-10)
Checks: 13 linear equalities, 8 nonlinear residuals, positivity margins, u <= caps,
Lambda >= ell (numeric box sampling), R >= D, and the C840-style quantified bounds
(widths, switch b range, radius ratios).
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
faces = ns['faces']; eq = ns['eq'][:, :42]; rhs = ns['rhs']
a0 = ns['x0'][:42]
R0 = float(shape(a0)[0])
ph = json.loads((OUT / 'phase1_runs.json').read_text())
mt = json.loads((OUT / 'mechanism_test.json').read_text())
cands = {'W1_cond00_delta0.05': np.array(ph['runs'][0]['a']),
         'W2_best': np.array(min(mt['runs'], key=lambda r: r['maxD1'])['a'])}

def caps_of(a):
    c = np.zeros(9)
    for i in range(9):
        e = tuple(sorted((i, (i + 1) % 9)))
        for t, f in enumerate(faces):
            if e[0] in f and e[1] in f:
                k = f.index(next(v for v in f if v not in e))
                c[i] = min(1.0, math.sin(a[3 * t + k]) / math.sin(a[33 + i]))
                break
    return c

res_out = {}
for name, a in cands.items():
    r, con, d = shape(a)
    g = np.exp(d['logg']); M = g.max(); u = g / M
    usw = u[11:20]; al, ww = d['alpha'], d['w']
    ell = np.array([math.sqrt(usw[(i - 1) % 9] ** 2 + usw[i] ** 2
                              - 2 * usw[(i - 1) % 9] * usw[i] * math.cos(al[i])) for i in range(9)])
    q = 2 * np.sin(ww / 2)
    c = caps_of(a)
    L1 = np.array([max(c[(i - 1) % 9], c[i],
                       math.sqrt(c[(i - 1) % 9] ** 2 + c[i] ** 2
                                 - 2 * c[(i - 1) % 9] * c[i] * math.cos(al[i]))) for i in range(9)])
    D = q / L1
    # numeric box-max check of Lambda >= ell (include axis corners explicitly)
    exc = []
    for i in range(9):
        c1, c2 = c[(i - 1) % 9], c[i]
        vals = [0.0, c1, c2, math.sqrt(c1 ** 2 + c2 ** 2 - 2 * c1 * c2 * math.cos(al[i]))]
        exc.append(float(max(vals) - L1[i]))
    pos = []
    for k in range(33):
        pos += [float(a[k]), float(math.pi - a[k])]
    for k in range(33, 42):
        pos += [float(a[k]), float(math.pi / 2 - a[k])]
    for i in range(9):
        pos += [float(al[i]), float(math.pi - al[i]), float(ww[i]), float(math.pi - ww[i])]
    row = dict(R=float(r), res_all21=float(abs(con).max()), res_8=float(abs(con[13:21]).max()),
               res_13=float(abs(eq @ a - rhs).max()),
               max_u_minus_caps=float((usw - c).max()), max_caps_excess=max(exc),
               R_minus_maxD=float(r - D.max()), maxD=float(D.max()),
               min_positivity=float(min(pos)), min_flat_margin=float((math.pi - al).min()),
               widths_deg=(ww * 180 / math.pi).tolist(), b_deg=(a[33:42] * 180 / math.pi).tolist(),
               u_sw=usw.tolist(), caps=c.tolist(), n_ceiling=int((u > 1 - 1e-9).sum()),
               C840_width_ok=bool(ww.min() >= 2 * math.pi - 16 * math.asin(0.37999)),
               C840_b_ok=bool(a[33:42].min() > 1 / 37999 and min(math.cos(x) for x in a[33:42]) >= 3 / 16),
               ratio_ok=bool((u.max() / u.min()) < 37999))
    res_out[name] = row
    print(name)
    for k, v in row.items():
        print('   %-18s %s' % (k, np.round(v, 6).tolist() if isinstance(v, list) else v))
print('R0 =', R0, ' C529 - maxD(W2) =', 0.37998385311983757 - res_out['W2_best']['maxD'])
(OUT / 'cited_witness_check.json').write_text(json.dumps(dict(R0=R0, rows=res_out), indent=2))
