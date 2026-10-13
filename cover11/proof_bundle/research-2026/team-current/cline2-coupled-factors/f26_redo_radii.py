"""cline2-coupled-factors f26: redo the realized-point dual evaluation WITHOUT mixing radii.

Two radii are in play and must not be mixed:
  * R = 19/50        -- the RELAXATION scale the lead's dual is built at (x = rho^2/R^2 <= 1),
                        so all factor v-values and coefficient rows use R;
  * R_cert           -- the radius of the saved candidate, at which it is a genuine cover
                        (R_cert < R).
On a realization at R_cert the primal identities hold at R_cert, so the correct way to
evaluate the dual (built at R) at that realization is to feed the realization's DIMENSIONLESS
data (r/R for every radius) into the R-parametrized rows and v-values.  Feeding rho/R_cert
while multiplying by R^2 (my earlier f9) is the mixed-radius bug the lead identified.

Self-consistency guard: the area identity S_sum = pi must reproduce at the radius actually
used.  We check it at R_cert.
"""
import numpy as np, json, math
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
pi = math.pi
R = 19/50

d = np.load(OUT/'realized.npz', allow_pickle=True)
W = d['W']; al = d['al']; L = d['L']; T = d['T']
C = d['C']; PK = d['PK']; slot_site = d['slot_site']
obj = json.loads((P.parent/'cline2-sharp-fan'/'out'/'certified_object_copy.json')
                 .read_text(encoding='utf-8-sig'))
RC = float(obj['certified_upper_bound_21digits'])
print(f'R (relaxation) = {R:.12f}   R_cert = {RC:.18f}   R_cert < R: {RC < R}')

row = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
z = np.array(row['z'])
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
ei = {e: k for k, e in enumerate(edges)}
adj = {e: [(t, next(k for k in f if k not in e))
           for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
sgn = {e: {adj[e][0][0]: 1.0} if len(adj[e]) == 1 else
        {adj[e][0][0]: 1.0, adj[e][1][0]: -1.0} for e in edges}
base = np.zeros(121)
base[0:9] = pi; base[9:11] = 2*pi; base[50:71] = pi; base[71] = -2*pi; base[112:121] = -pi
CZ = float(base @ z)
print(f'const.z0 = {CZ:.9f}')

# --- area identity check at R_cert (no R mixed in) ---
ch = np.linalg.norm(C[slot_site]-C[np.roll(slot_site, -1)], axis=1)
b = np.arcsin(np.clip(ch/2/RC, -1, 1))
Ssum = sum(RC*RC*math.sin(al[k])/2 + (W[k]-math.sin(W[k]))/2 for k in range(9))
print(f'area identity at R_cert: sum of sector kernels = {Ssum:.12f}   pi = {pi:.12f}   '
      f'diff = {Ssum-pi:+.3e}')
print('   (this must be ~0 for a genuine cover at R_cert; if not, the reconstruction '
      'radii are wrong again)')


def site(lab):
    return C[slot_site[lab]] if lab < 9 else C[{9: 0, 10: 2}[lab]]


def circum(f):
    a, bb, c = site(f[0]), site(f[1]), site(f[2])
    A = bb-a; B = c-a
    dd = 2*(A[0]*B[1]-A[1]*B[0])
    p = a+np.array([(B[1]*(A@A)-A[1]*(B@B))/dd, (A[0]*(B@B)-B[0]*(A@A))/dd])
    return p, float(np.linalg.norm(p-a))


def ang_at(f, s):
    o = [x for x in f if x != s]
    u1 = site(o[0])-site(s); u2 = site(o[1])-site(s)
    return math.acos(np.clip(u1 @ u2/np.linalg.norm(u1)/np.linalg.norm(u2), -1, 1))


def realized_total(Rrel):
    """evaluate the lead's dual rows at the realization, using RELAXATION radius Rrel for
    the v-values and dimensionless ratios rho/Rrel, 1 (switches), r/Rrel for endpoints."""
    tot = CZ
    detail = []
    for t, f in enumerate(faces):
        p, rho = circum(f)
        x = (rho/Rrel)**2
        val = 2*Rrel*Rrel*x*math.prod([math.sin(ang_at(f, s)) for s in f])
        r = np.zeros(121)
        for i in f:
            e = tuple(sorted(j for j in f if j != i)); k = ei[e]
            sg = sgn[e][t]
            r[i] -= ang_at(f, i); r[50+k] -= ang_at(f, i)
            r[11+k] += sg*x*math.sin(ang_at(f, i))**2
            r[73+k] += sg*math.sqrt(x)*math.sin(ang_at(f, i))
        tot += val + r @ z
        detail.append((f'face{t}', val+r@z, x))
    for k in range(9):
        i, j = k, (k+1) % 9          # SLOT labels 0..8 are the ring sites
        e = tuple(sorted((i, j))); kk = ei[e]
        bb = b[k]
        # switch radius at P_k in units of Rrel: the switch is at distance RC from the
        # rings (covering radius at RC); its own radius relative to the relaxation is RC/Rrel
        y2 = (RC/Rrel)**2
        val = Rrel*Rrel*y2*math.sin(2*bb)/2
        r = np.zeros(121)
        r[i] += bb; r[j] += bb; r[50+kk] -= bb; r[112+k] += 2*bb
        r[11+kk] -= y2*math.sin(bb)**2; r[73+kk] -= math.sqrt(y2)*math.sin(bb)
        r[32+2*i+1] += y2; r[32+2*j] += y2
        r[94+2*i+1] += math.sqrt(y2); r[94+2*j] += math.sqrt(y2)
        tot += val + r @ z
        detail.append((f'switch{k}', val+r@z, y2))
    for k in range(9):
        a_ = al[k]; w_ = W[k]
        e_ = RC/Rrel                        # endpoint copies: switches at distance RC
        ww = 2*math.asin(min(1.0, Rrel*math.sqrt(2*e_*e_-2*e_*e_*math.cos(a_))/2))
        S = Rrel*Rrel*e_*e_*math.sin(a_)/2 + (ww-math.sin(ww))/2
        r = np.zeros(121)
        r[112+(k-1) % 9] += L[k]+ww/2
        r[112+k] += T[k]+ww/2
        r[k] -= a_
        r[32+2*k] -= e_*e_; r[32+2*k+1] -= e_*e_
        r[71] += ww
        r[94+2*k] -= e_; r[94+2*k+1] -= e_
        tot += S + r @ z
        detail.append((f'ring{k}', S+r@z, e_))
    return tot, detail


for Rrel, tag in [(R, 'R=19/50'), (RC, 'R_cert')]:
    tot, det = realized_total(Rrel)
    print(f'\n--- realization evaluated with relaxation radius {tag} ---')
    print(f'  const.z0 + sum_f(row_f) = {tot:.12f}   pi = {pi:.12f}   '
          f'tot - pi = {tot-pi:+.4e}')
    if tag == 'R=19/50':
        print('  per-factor realized contributions:')
        for n, v, xv in det:
            print(f'     {n:9s} {v: .9f}   (arg x/e^2 = {xv:.9f})')
        print('  face contributions sum =',
              sum(v for n, v, _ in det if n.startswith('face')))
        print('  switch contributions sum =',
              sum(v for n, v, _ in det if n.startswith('switch')))
        print('  ring contributions sum =',
              sum(v for n, v, _ in det if n.startswith('ring')))
print('\nNote: "u=v=1 at R_cert" means the switches are at distance exactly R_cert from '
      'their rings; in units of R the square is (RC/R)^2 = '
      f'{(RC/R)**2:.10f}, NOT 1.')
