"""Debug the edge-ratio matrix: compare Rlat[f,h] with log(u_h/u_f) for all 21 edges at a witness."""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
faces = ns['faces']; edges = ns['edges']
data = json.loads((OUT / 'mechanism_test.json').read_text())
best = min(data['runs'], key=lambda r: r['maxD1'])
a = np.array(best['a'])
r, con, d = shape(a)
g = np.exp(d['logg']); M = g.max(); u = g / M
print('u =', np.round(u, 9).tolist())
bad = []
for ei, (i, j) in enumerate(edges):
    adj = []
    for t, f in enumerate(faces):
        if i in f and j in f:
            k = f.index(next(v for v in f if v not in (i, j)))
            adj.append((t, a[3 * t + k]))
    if len(adj) == 2:
        (t1, A1), (t2, A2) = adj
        lr = math.log(math.sin(A1)) - math.log(math.sin(A2))
        emp = math.log(u[t2]) - math.log(u[t1])
        bad.append((ei, (i, j), 'internal', t1, t2, lr, emp, lr - emp))
    else:
        (t1, A1), = adj
        bi = next(b for b in range(9) if {b, (b + 1) % 9} == {i, j})
        lr = math.log(math.sin(A1)) - math.log(math.sin(a[33 + bi]))
        emp = math.log(u[11 + bi]) - math.log(u[t1])
        bad.append((ei, (i, j), 'boundary', t1, 11 + bi, lr, emp, lr - emp))
for row in bad:
    print('edge%2d %s %s  f=%2d g=%2d  rlat=%+.6f  empirical=%+.6f  diff=%+.2e'
          % (row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7]))
print('max |diff| =', max(abs(x[7]) for x in bad))
