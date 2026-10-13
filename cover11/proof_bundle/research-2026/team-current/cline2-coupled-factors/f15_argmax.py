"""cline2-coupled-factors f15: where does the dual's value actually come from?

For the lead's feasible z0 on q0(6,7) we report, factor by factor:
  * the sampled maximum and its argmax,
  * for sector (ring) factors: the argmax (alpha,u,v) and its deviation |u-v|,
  * the value obtained by restricting the sector to the PROVED-legal diagonal u = v
    (f12: u_k = v_k identically), and to the realized point.
This localizes which factors carry the 3.386e-2 that any sharper coupling must recover.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi
N, NR, NA = 36, 12, 96

row = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
z = np.array(row['z'])
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
ei = {e: k for k, e in enumerate(edges)}
side0, rr0, kap0, lam0, lin0, cl0 = 11, 32, 50, 71, 73, 112
nz = 121
adj = {e: [(t, next(k for k in f if k not in e))
           for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
sgn = {e: {adj[e][0][0]: 1.0} if len(adj[e]) == 1 else
        {adj[e][0][0]: 1.0, adj[e][1][0]: -1.0} for e in edges}
base = np.zeros(nz)
base[0:9] = pi; base[9:11] = 2*pi; base[kap0:lam0] = pi; base[lam0] = -2*pi
base[cl0:cl0+9] = -pi
print(f'const.z = {float(base@z):.9f}')
tot = float(base @ z)

# ---- faces ----
aa = np.array([(i*pi/N, j*pi/N) for i in range(N+1) for j in range(N+1-i)])
xx = np.linspace(0, 1, 31)**2
agg = np.tile(np.c_[aa, pi-aa[:, 0]-aa[:, 1]], (len(xx), 1))
xl = np.repeat(xx, len(aa))
print('\nFACE factors (value maximized over x in [0,1] and the angle simplex):')
ftot = 0
for t, f in enumerate(faces):
    v = 2*R*R*xl*np.prod(np.sin(agg), axis=1)
    M = np.zeros((len(v), nz))
    for k, i in enumerate(f):
        e = tuple(sorted(j for j in f if j != i)); ee = ei[e]
        sg = 1 if adj[e][0][0] == t else -1
        M[:, i] -= agg[:, k]; M[:, kap0+ee] -= agg[:, k]
        M[:, side0+ee] += sg*xl*np.sin(agg[:, k])**2
        M[:, lin0+ee] += sg*np.sqrt(xl)*np.sin(agg[:, k])
    vals = v+M@z
    j = int(np.argmax(vals)); ftot += vals[j]
    print(f'   face{t} {f}: {vals[j]: .9f}  argmax x={xl[j]:.6f}, '
          f'angles=({agg[j,0]:.4f},{agg[j,1]:.4f},{agg[j,2]:.4f})')

# ---- switches ----
print('\nSWITCH factors:')
stot = 0
for bi in range(9):
    i, j = bi, (bi+1) % 9; e = tuple(sorted((i, j))); ee = ei[e]
    b = np.tile(np.linspace(0, pi/2, 4*N+1), 31)
    x = np.repeat(np.linspace(0, 1, 31)**2, 4*N+1)
    v = R*R*x*np.sin(2*b)/2
    M = np.zeros((len(v), nz))
    M[:, cl0+bi] += 2*b; M[:, i] += b; M[:, j] += b; M[:, kap0+ee] -= b
    M[:, side0+ee] -= x*np.sin(b)**2; M[:, lin0+ee] -= np.sqrt(x)*np.sin(b)
    M[:, rr0+2*i+1] += x; M[:, rr0+2*j] += x
    M[:, lin0+21+2*i+1] += np.sqrt(x); M[:, lin0+21+2*j] += np.sqrt(x)
    vals = v+M@z
    jj = int(np.argmax(vals)); stot += vals[jj]
    print(f'   switch{bi}: {vals[jj]: .9f}  argmax b={b[jj]:.6f} (pi/2={pi/2:.4f}), '
          f'x={x[jj]:.6f}')

# ---- rings, three domains ----
print('\nRING factors: full domain vs proved-legal diagonal u=v vs realized point')
grid = np.array([(a, u, v) for a in np.linspace(0, pi, NA+1)
                 for u in np.linspace(0, 1, NR+1) for v in np.linspace(0, 1, NR+1)])
a, u, v = grid.T
ch = R*np.sqrt(np.maximum(0, u*u+v*v-2*u*v*np.cos(a)))
w = 2*np.arcsin(np.minimum(1.0, ch/2))
S = R*R*u*v*np.sin(a)/2 + (w-np.sin(w))/2
left = np.arctan2(v*np.sin(a), u-v*np.cos(a))
right = np.arctan2(u*np.sin(a), v-u*np.cos(a))
diag_grid = np.array([(al, e, e) for al in np.linspace(0, pi, 4*N+1)
                      for e in np.linspace(0, 1, 16*NR+1)])
ad, ed, _ = diag_grid.T
wd = 2*np.arcsin(np.minimum(1.0, R*ed*np.sin(ad/2)))
Sd = R*R*ed*ed*np.sin(ad)/2 + (wd-np.sin(wd))/2
d = np.load(OUT/'realized.npz', allow_pickle=True)
W = d['W']; alr = d['al']; Rc = float(d['Rc'])
rtot = 0; rtot_diag = 0; rtot_real = 0
for i in range(9):
    M = np.zeros((len(a), nz))
    M[:, cl0+(i-1) % 9] = left + w/2; M[:, cl0+i] = right + w/2
    M[:, i] = -a; M[:, rr0+2*i] = -u*u; M[:, rr0+2*i+1] = -v*v; M[:, lam0] = w
    M[:, lin0+21+2*i] = -u; M[:, lin0+21+2*i+1] = -v
    vals = S+M@z
    j = int(np.argmax(vals)); rtot += vals[j]
    Md = np.zeros((len(ad), nz))
    Md[:, cl0+(i-1) % 9] = 0; Md[:, cl0+i] = 0
    Md[:, i] = -ad; Md[:, rr0+2*i] = -ed*ed; Md[:, rr0+2*i+1] = -ed*ed
    Md[:, lam0] = wd; Md[:, lin0+21+2*i] = -ed; Md[:, lin0+21+2*i+1] = -ed
    valsd = Sd+Md@z
    jd = int(np.argmax(valsd)); rtot_diag += valsd[jd]
    ar = alr[i]
    wr = 2*math.asin(min(1.0, R*math.sin(ar/2)))
    Sr = R*R*math.sin(ar)/2 + (wr-math.sin(wr))/2
    rr = np.zeros(nz)
    rr[i] = -ar; rr[rr0+2*i] = -1.0; rr[rr0+2*i+1] = -1.0
    rr[lam0] = wr; rr[lin0+21+2*i] = -1.0; rr[lin0+21+2*i+1] = -1.0
    vr = Sr+rr@z
    rtot_real += vr
    print(f'   ring{i}: full {vals[j]: .9f} at (a={a[j]:.4f},u={u[j]:.6f},v={v[j]:.6f},'
          f'|u-v|={abs(u[j]-v[j]):.5f})')
    print(f'          diagonal {valsd[jd]: .9f} at (a={ad[jd]:.4f},e={ed[jd]:.6f})')
    print(f'          realized {vr: .9f} at (a={ar:.4f},e=1)   '
          f'max(0,full-diag)={max(0.0,float(vals[j]-valsd[jd])):.3e}')
print(f'\nTOTALS: faces {ftot:.9f} + switches {stot:.9f} + rings full {rtot:.9f} '
      f'+ const {float(base@z):.9f} = {ftot+stot+rtot+float(base@z):.9f}')
print(f'        rings on the legal diagonal {rtot_diag:.9f}  (gain in bound '
      f'{rtot-rtot_diag:+.3e})')
print(f'        rings at the realized point {rtot_real:.9f}  (forced share '
      f'{rtot-rtot_real:+.3e})')
np.savez(OUT/'f15.npz', ftot=ftot, stot=stot, rtot=rtot, rtot_diag=rtot_diag,
         rtot_real=rtot_real, const=float(base@z))
