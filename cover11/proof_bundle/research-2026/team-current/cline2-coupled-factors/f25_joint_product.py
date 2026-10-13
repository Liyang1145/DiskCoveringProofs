"""cline2-coupled-factors f25: the JOINT second-moment (product) row, done correctly.

Why the naive product rows in f20/f23 went unbounded: a multiplier s_f with coefficient
sin^2 A_f >= 0 is a free direction unless it is PINNED.  The exact geometry pins it:

    (x_f sin^2 A_f)(x_g sin^2 B_g) = (d_e/2R)^4 =: K_e^4       on every realization,

so the product of the two partners is bounded, which is exactly the missing bound.

Dual form implemented here (one joint row per internal edge):
    s_f, s_g >= 0 ;  s_f sin^2 A_f + s_g sin^2 B_g <= sqrt( s_f s_g ) * 2 K_e^2 / (R^2 x)
is NOT used; instead we use the polynomial form valid for ALL (x_f,x_g) satisfying the
product identity:
    s_f sin^2 A_f + s_g sin^2 B_g  <=  2 sqrt( s_f s_g ) * (d_e/2R)^2 / (R sqrt(x_f x_g))
For a fixed z we compute, by maximizing over the face domains at the current values of the
non-moment multipliers, the single nonlinear inequality
    max_domain [ sqrt(s_f s_g) * 2 (rho_f sin A_f)(rho_g sin B_g) / (R^2 sqrt(x_f x_g)) ]
        - s_f sin^2 A_f - s_g sin^2 B_g   <=  0
and add it as one cut.  Because the left side couples s_f and s_g multiplicatively, the LP
remains bounded; the bound is then reported and compared with the lead's 3.175702558.

Sampled domains again: NOT a certificate, a diagnostic for whether the joint row has grip.
"""
import numpy as np, json, math, sys, time
from pathlib import Path
from scipy.optimize import linprog
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi
N, NR, NA = 36, 12, 96

row = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
z0lead = np.array(row['z'])
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
ei = {e: k for k, e in enumerate(edges)}
adj = {e: [(t, next(k for k in f if k not in e))
           for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
sgn = {e: {adj[e][0][0]: 1.0} if len(adj[e]) == 1 else
        {adj[e][0][0]: 1.0, adj[e][1][0]: -1.0} for e in edges}
internal = [k for k in range(21) if len(adj[edges[k]]) == 2]
slot = {k: j for j, k in enumerate(internal)}
NS = 2*len(internal)
NZ = 121 + NS
B = np.zeros(NZ)
B[0:9] = pi; B[9:11] = 2*pi; B[50:71] = pi; B[71] = -2*pi; B[112:121] = -pi

# --- sample sets, kept per factor, with the geometry needed for the joint row ---
aa = np.array([(i*pi/N, j*pi/N) for i in range(N+1) for j in range(N+1-i)])
xx = np.linspace(0, 1, 40)**2                    # x-grid, denser than the lead's 31
SAMP = {}
for t, f in enumerate(faces):
    ang = np.tile(np.c_[aa, pi-aa[:, 0]-aa[:, 1]], (len(xx), 1))
    x = np.repeat(xx, len(aa))
    SAMP[('face', t)] = dict(ang=ang, x=x, v=2*R*R*x*np.prod(np.sin(ang), axis=1))
for bi in range(9):
    b = np.tile(np.linspace(0, pi/2, 4*N+1), len(xx))
    x = np.repeat(xx, 4*N+1)
    SAMP[('switch', bi)] = dict(b=b, x=x, v=R*R*x*np.sin(2*b)/2)
grid = np.array([(a, u, v) for a in np.linspace(0, pi, NA+1)
                 for u in np.linspace(0, 1, NR+1) for v in np.linspace(0, 1, NR+1)])
ga, gu, gv = grid.T
gq = np.maximum(0, gu*gu+gv*gv-2*gu*gv*np.cos(ga))
gch = R*np.sqrt(gq)
gw = 2*np.arcsin(np.minimum(1.0, gch/2))
gS = R*R*gu*gv*np.sin(ga)/2 + (gw-np.sin(gw))/2
gleft = np.arctan2(gv*np.sin(ga), gu-gv*np.cos(ga))
gright = np.arctan2(gu*np.sin(ga), gv-gu*np.cos(ga))


def rows_for_factor(z, key):
    """returns (name, vals, Mz) with Mz the multiplier part at every sample"""
    Mz = np.zeros(len(SAMP[key]['v']))
    if key[0] == 'face':
        t = key[1]; f = faces[t]; D = SAMP[key]
        for k, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ee = ei[e]
            sg = 1 if adj[e][0][0] == t else -1
            s = np.sin(D['ang'][:, k])
            Mz += -(z[i]+z[50+ee])*D['ang'][:, k]
            Mz += sg*D['x']*s*s*z[11+ee]
            Mz += sg*np.sqrt(D['x'])*s*z[73+ee]
        return f'face{t}', D['v']+Mz, D, Mz
    if key[0] == 'switch':
        bi = key[1]; i, j = bi, (bi+1) % 9; e = tuple(sorted((i, j))); ee = ei[e]
        D = SAMP[key]; b = D['b']; x = D['x']
        Mz += (z[i]+z[j]-z[50+ee]+2*z[112+bi])*b
        Mz += -(x*np.sin(b)**2)*z[11+ee]
        Mz += -(np.sqrt(x)*np.sin(b))*z[73+ee]
        Mz += x*(z[32+2*i+1]+z[32+2*j])
        Mz += np.sqrt(x)*(z[94+2*i+1]+z[94+2*j])
        return f'switch{bi}', D['v']+Mz, D, Mz
    i = key[1]
    Mz = -ga*z[i] - (gu*gu)*z[32+2*i] - (gv*gv)*z[32+2*i+1] + gw*z[71]
    Mz += -gu*z[94+2*i] - gv*z[94+2*i+1]
    Mz += (gleft+gw/2)*z[112+(i-1) % 9] + (gright+gw/2)*z[112+i]
    return f'ring{i}', gS+Mz, dict(ang=np.c_[ga, np.zeros_like(ga), np.zeros_like(ga)],
                                   x=gq*0+gq, q=gq), Mz


def joint_row_values(z, se, s):
    """For internal edge with local index j: partner multipliers are s[2j] (first face)
    and s[2j+1] (second face).  Returns max over the paired faces of
        sqrt(s0 s1) * 2 (rho_f sin A_f)(rho_g sin B_g)/(R^2 sqrt(x_f x_g))
          - s0 sin^2 A_f - s1 sin^2 B_g."""
    k = internal[j_local]
    pass


# --- LP with column generation; the joint row is added as a linear cut at its argmax ---
def evaluate(z):
    tot = float(B[:121] @ z[:121])
    for t in range(11):
        tot += float(np.max(rows_for_factor(z, ('face', t))[1]))
    for b in range(9):
        tot += float(np.max(rows_for_factor(z, ('switch', b))[1]))
    for i in range(9):
        tot += float(np.max(rows_for_factor(z, ('ring', i))[1]))
    return tot


print('calibration: bound at (z0, s=0) =', evaluate(np.r_[z0lead, np.zeros(NS)]),
      ' lead =', row['sample_upper'])
