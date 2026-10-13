"""cline2-coupled-factors f1: structural probe of the q0(6,7) [start0 span4] closure factor dual.

MECHANISM UNDER TEST: first-moment (linear-in-half-side) matching multipliers.

Exact basis (C816 shared-side identity, SHARED-FACTOR-DUAL.md):
    rho_f sin A = rho_g sin B = d_e/2    on every shared edge,
with positive radii and angles in (0,pi).  Therefore BOTH
    (i)  rho_f^2 sin^2 A = rho_g^2 sin^2 B     (squared / second-moment adjoint), and
    (ii) rho_f   sin A   = rho_g   sin B       (first-moment / linear-in-x adjoint)
are exact on a genuine configuration.  The lead's q0_closure_dual.py carries only the
squared adjoint (variable block `side`) and leaves its 18 `lin` multipliers with no
face/switch counterpart -- indeed q0_closure_dual_certificate_0_3.json coefficients
73..111 are all exactly 0.  Here those rows are opened: 21 new free first-moment
multipliers L[e] entering each face as +/-(sgn_e) sin A_k and each switch as -sin b.

This script is a PROPOSER + DIAGNOSTIC.  Sampled maximizers are NOT certificates.

Calibration: with L == 0 and lin == 0 the architecture reduces to the lead's and must
reproduce q0_closure_dual_0_4.json sample_upper = 3.17570255754794.
"""
import numpy as np, json, math, sys, time
from pathlib import Path
from scipy.optimize import linprog
from scipy import sparse

P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
OUT.mkdir(exist_ok=True)
R = 19/50
pi = math.pi


def lead_spec(start, span):
    return json.loads((LEAD / f'q0_closure_dual_{start}_{span}.json').read_text())


def _stack(rows, cols, dat, n, nz):
    """dat entries may be length-n arrays or scalars."""
    R_, C_, D_ = [], [], []
    for r, c, d in zip(rows, cols, dat):
        r = np.asarray(r)
        d = np.full(len(r), float(d), dtype=float) if np.ndim(d) == 0 else np.asarray(d, float)
        R_.append(r); C_.append(np.full(len(r), int(c), dtype=int)); D_.append(d)
    return sparse.csr_matrix((np.concatenate(D_), (np.concatenate(R_), np.concatenate(C_))),
                             shape=(n, nz))


class Prob:
    """Lead variable layout verbatim + 21 new first-moment multipliers at pos..pos+20.

    Lead layout: 0:9 mu_ring, 9:11 mu_hub, 11:32 side(21), 32:50 rr(2*9),
    50:71 kappa(21)>=0, 71 lambda, 72 eta(==0 for q0), 73:94 lin_side(21),
    94:112 lin_radius(18), 112:121 closure h(9).
    NOTE: the lead's face formula routes its 11 mu slots to slots 0:11 while the hub
    triangles are t=9,10 -> slots 9,10.  Identical here.
    """

    def __init__(self, start, span, NA=96, NR=12, N=36):
        row = lead_spec(start, span)
        self.start, self.span = start, span
        self.faces = [tuple(f) for f in row['faces']]
        self.edges = [tuple(e) for e in row['edges']]
        self.ne, self.nf = len(self.edges), len(self.faces)
        assert (self.ne, self.nf) == (21, 11)
        self.side, self.rr, self.kap = 11, 32, 50
        self.lam, self.eta, self.lin_side, self.lin_rad, self.cl = 71, 72, 73, 94, 112
        self.pos = 121
        self.nz = self.pos + self.ne                     # 142
        assert all(a < b for a, b in self.edges), 'lead edge list is stored sorted'
        self.ei = {e: k for k, e in enumerate(self.edges)}
        self.adj, self.sgn = [], []                      # per edge: faces and +1/-1 signs
        for k, e in enumerate(self.edges):
            hit = [(t, next(j for j in f if j not in e))
                   for t, f in enumerate(self.faces) if e[0] in f and e[1] in f]
            assert 1 <= len(hit) <= 2, (e, hit)
            self.adj.append(hit)
            ts = sorted(t for t, _ in hit)
            self.sgn.append({ts[0]: 1.0} if len(ts) == 1 else {ts[0]: 1.0, ts[1]: -1.0})
        self.base = np.zeros(self.nz)
        self.base[0:9] = pi
        self.base[9:11] = 2*pi
        self.base[self.kap:self.lam] = pi
        self.base[self.lam] = -2*pi
        self.base[self.cl:self.cl+9] = -pi
        # ---- sample domains ----
        self.face_pts = np.array([(i*pi/N, j*pi/N) for i in range(N+1) for j in range(N+1-i)])
        self.sw_pts = np.linspace(0, pi/2, 4*NA+1)
        a = np.linspace(0, pi, NA+1); u = np.linspace(0, 1, NR+1)
        A, U, V = np.meshgrid(a, u, u, indexing='ij')
        self.ring_pts = np.stack([A.ravel(), U.ravel(), V.ravel()], axis=1)
        self.qmin = 4*math.sin(pi - 8*math.asin(R))**2/R**2

    # ---------------- factor coefficient builders, sparse (n, nz) ----------------
    def face(self, t, th=None):
        th = self.face_pts if th is None else th
        a, b = th[:, 0], th[:, 1]; c = pi - a - b
        ok = (a >= 0) & (b >= 0) & (c >= 0)
        a, b, c = a[ok], b[ok], c[ok]
        n = len(a)
        rows, cols, dat = [], [], []
        for kk, ang in enumerate([a, b, c]):
            i = self.faces[t][kk]
            e = tuple(sorted(j for j in self.faces[t] if j != i)); k = self.ei[e]
            sg = self.sgn[k][t]; s = np.sin(ang)
            for col, d in [(i, -ang), (self.kap+k, -ang), (self.side+k, sg*s*s),
                           (self.lin_side+k, sg*s), (self.pos+k, sg*s)]:
                rows.append(np.arange(n)); cols.append(col); dat.append(d)
        return _stack(rows, cols, dat, n, self.nz), 2*R*R*np.sin(a)*np.sin(b)*np.sin(c)

    def switch(self, bi, nb=2048):
        b = self.sw_pts if nb is None else np.linspace(0, pi/2, nb)
        i, j = bi, (bi+1) % 9
        k = self.ei[tuple(sorted((i, j)))]
        n = len(b)
        rows = [np.arange(n)]*7
        cols = [i, j, self.kap+k, self.cl+bi, self.side+k, self.lin_side+k, self.pos+k]
        dat = [b, b, -b, 2*b, -np.sin(b)**2, -np.sin(b), -np.sin(b)]
        return _stack(rows, cols, dat, n, self.nz), R*R*np.sin(2*b)/2

    def ring(self, i, pts=None):
        pts = self.ring_pts if pts is None else pts
        al, u, v = pts[:, 0], pts[:, 1], pts[:, 2]
        q = (u-v)**2 + 4*u*v*np.sin(al/2)**2
        keep = q >= self.qmin
        al, u, v, q = al[keep], u[keep], v[keep], q[keep]
        w = 2*np.arcsin(np.minimum(1.0, R*np.sqrt(q)/2))
        S = R*R*u*v*np.sin(al)/2 + (w - np.sin(w))/2
        kr = self.ei[tuple(sorted((i, (i+1) % 9)))]
        kl = self.ei[tuple(sorted(((i-1) % 9, i)))]
        n = len(al)
        rows = [np.arange(n)]*7
        cols = [self.lin_rad+2*i, self.lin_rad+2*i+1, self.rr+2*i, self.rr+2*i+1,
                self.lam, self.pos+kr, self.pos+kl]
        dat = [-u, -v, -u*u, -v*v, w, -u, -v]
        return _stack(rows, cols, dat, n, self.nz), S


def max_j(A, z, v):
    tot = v + A @ z
    j = int(np.argmax(tot))
    return float(tot[j]), j


def evaluate(pr, facs, sws, rngs, z, detail=False):
    tot = float(pr.base @ z)
    det = []
    for name, (A, v) in [(f'face{t}', facs[t]) for t in range(11)] + \
                        [(f'switch{b}', sws[b]) for b in range(9)] + \
                        [(f'ring{i}', rngs[i]) for i in range(9)]:
        val, j = max_j(A, z, v)
        tot += val
        det.append((name, val, j))
    return (tot, det) if detail else tot


def bound_table(pr, facs, sws, rngs, z):
    """per-factor value at the maximizer, plus factor identity of the argmax point."""
    rows = []
    for name, (A, v), extra in [(f'face{t}', facs[t], None) for t in range(11)] + \
                              [(f'switch{b}', sws[b], None) for b in range(9)]:
        val, j = max_j(A, z, v)
        rows.append((name, val, j, None))
    for i, (A, v) in enumerate(rngs):
        val, j = max_j(A, z, v)
        pts = pr.ring_pts
        q = (pts[:, 1]-pts[:, 2])**2 + 4*pts[:, 1]*pts[:, 2]*np.sin(pts[:, 0]/2)**2
        keep = q >= pr.qmin
        rows.append((f'ring{i}', val, j, pts[keep][j]))
    return rows


def build(start, span):
    pr = Prob(start, span)
    facs = [pr.face(t) for t in range(11)]
    sws = [pr.switch(b) for b in range(9)]
    rngs = [pr.ring(i) for i in range(9)]
    return pr, facs, sws, rngs


def main():
    start, span = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (0, 4)
    t0 = time.time()
    pr, facs, sws, rngs = build(start, span)
    print(f'built ({start},{span}) qmin={pr.qmin:.6f} nz={pr.nz} t={time.time()-t0:.1f}s',
          flush=True)
    row = lead_spec(start, span)
    z0 = np.concatenate([np.array(row['z']), np.zeros(21)])
    tot, det = evaluate(pr, facs, sws, rngs, z0, detail=True)
    print(f'CALIBRATION lead-z (L=0): bound={tot:.9f}   lead sample_upper='
          f'{row["sample_upper"]:.9f}   delta={tot-row["sample_upper"]:+.3e}')
    for n, v, j in det:
        print(f'   {n:10s} {v: .9f}  argmax#{j}')
    np.save(OUT / f'z0_{start}_{span}.npy', z0)
    print(f'elapsed {time.time()-t0:.1f}s')


if __name__ == '__main__':
    main()
