"""Check the exact sine-law matching identities for boundary edges (site face <-> switch),
and pin the geometric meaning of the model's b_i variable (half- vs full apex angle)."""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
W = Path(__file__).parent; LEAD = W.parent / 'lead'
zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
a0 = ns['x0'][:42]
C = ns['c']; faces = ns['faces']; edges = ns['edges']
R, con, det = shape(a0)
g = np.exp(det['logg']); M = g.max()
sw = list(range(11, 20))
rows = []
for i in range(9):
    j = (i + 1) % 9
    # geometric switch triangle
    ci, cj = C[i], C[j]
    d = np.linalg.norm(cj - ci); m = (ci + cj) / 2
    n = np.array([(cj - ci)[1], -(cj - ci)[0]]) / d
    l = -m @ n + math.sqrt((m @ n) ** 2 + 1 - m @ m)
    P = m + l * n
    v1, v2 = ci - P, cj - P
    apex = math.acos(np.clip(v1 @ v2 / np.linalg.norm(v1) / np.linalg.norm(v2), -1, 1))
    rho_sw = np.linalg.norm(P - ci)
    bb = math.atan2(d / 2, l)
    # site face containing the boundary edge
    for t, f in enumerate(faces):
        if i in f and j in f:
            k = f.index(next(v for v in f if v not in (i, j)))
            Aang = a0[3 * t + k]; rho_f = None
            p = C[f]
            vv = np.linalg.solve(2 * (p[1:] - p[0]), (p[1:] ** 2).sum(1) - (p[0] ** 2).sum())
            rho_f = np.linalg.norm(vv - p[0])
            break
    rows.append(dict(i=i, apex_deg=apex * 180 / math.pi, b_deg=a0[33 + i] * 180 / math.pi,
                     twice_b_deg=2 * a0[33 + i] * 180 / math.pi,
                     atan2_deg=bb * 180 / math.pi,
                     A_face_deg=Aang * 180 / math.pi,
                     sinA=math.sin(Aang), sin_b=math.sin(a0[33 + i]), sin_2b=math.sin(2 * a0[33 + i]),
                     gamma_sw=g[11 + i], gamma_face=g[t], rho_sw=rho_sw, rho_face=rho_f,
                     lhs_face=rho_f * math.sin(Aang), rhs_sw_sinb=rho_sw * math.sin(a0[33 + i]),
                     rhs_sw_sin2b=rho_sw * math.sin(2 * a0[33 + i])))
for r in rows:
    print({k: (round(v, 12) if isinstance(v, float) else v) for k, v in r.items()})
(Path(__file__).parent / 'out' / 'sine_check.json').write_text(json.dumps(rows, indent=2))
print('max |ceq| =', abs(con).max())
