"""stress_core.py — 通用「网络应力 + Schur + 常数 Hessian 次式」核（n14 路线诊断用）。

表示：节点 = anchors(固定单位圆上) + sites + witnesses(自由)；边 = 活跃约束。
  * 应力：自由节点的向量平衡 Σ_e α_e (z_e − z_a) = 0（每条活跃边长度相同 ⇒ 用原始向量即等价于单位方向）
    用 LP 找**严格正**的应力（nullspace ∩ 正锥）。
  * Schur：全图加权 Laplacian，消去自由节点（主元顺序任意，上三角更新）→ anchor 块 Schur 补 Q，q_ij = −Q_ij ≥ 0。
  * 常数次式 M：c_d 给定时 M_ij = −2 q_ij c_{d_ij} (i≠j)，M_ii = Σ_j 2 q_ij c_{d_ij}；M·1 = 0 恒等。
  * 全域下界：H(θ) ⪰ M 当且仅当对每对 (i,j)：cos(θ_i−θ_j) ≥ c_{d_ij}（由域的 gap 界给出）。
    本核只负责“给定 c_d 时 M 在 1⊥ 上的正负与余量”。
"""
from fractions import Fraction as F
import json
import mpmath as mp
import numpy as np


# ---------------------------------------------------------------- exact constants
def cos_minorants(U_rat, dmax, L_bound_check=True):
    """c_d = T_d(1-2U^2) for dL<pi; for d with d*L>=pi return None (caller must replace)."""
    U = F(U_rat)
    c1 = 1 - 2 * U * U
    out = {1: c1}
    prev, cur = F(1), c1
    for d in range(2, dmax + 1):
        nxt = 2 * c1 * cur - prev
        out[d] = nxt
        prev, cur = cur, nxt
    return out


def L_and_defect(U, dps=60):
    mp.mp.dps = dps
    Um = mp.mpf(U)
    L = 2 * mp.asin(Um)
    defect = 10 * L - 2 * mp.pi       # n=10 anchors: 10L - 2pi
    return L, defect


# ---------------------------------------------------------------- network helpers
class Net:
    """anchors: list of (x,y) on S^1 ; sites: list of (x,y) ; faces: list of (i,j,k) site triples."""

    def __init__(self, anchors, sites, faces):
        self.A = [(mp.mpf(x) if not isinstance(x, str) else mp.mpf(x), mp.mpf(y) if not isinstance(y, str) else mp.mpf(y)) for x, y in anchors]
        self.S = [(mp.mpf(x), mp.mpf(y)) for x, y in sites]
        self.faces = [tuple(f) for f in faces]
        self.na, self.ns, self.nf = len(self.A), len(self.S), len(self.faces)
        # nodes: 0..na-1 anchors, na..na+ns-1 sites, na+ns..+nf-1 witnesses (witness coords set later)
        self.edges = []
        self.anchor_owners = [[] for _ in range(self.na)]
        self.W = None

    def add_anchor_edges(self, owners):
        """owners[i] = (site_index, site_index) for anchor i."""
        for i, (s1, s2) in enumerate(owners):
            for s in (s1, s2):
                self.edges.append((i, self.na + s))
                self.anchor_owners[i].append(s)

    def add_face_edges(self, witnesses):
        """witnesses[k] = (x,y) position of face k's witness; face k = self.faces[k]."""
        base = self.na + self.ns
        self.Wpos = [tuple(w) for w in witnesses]
        for k, f in enumerate(self.faces):
            for s in f:
                self.edges.append((base + k, self.na + s))

    # -------------------------------------------------- stress LP
    def positive_stress(self):
        """max t s.t. equilibrium at every free node, alpha_e >= t, sum alpha = 1."""
        n = self.na + self.ns + self.nf
        free = list(range(self.na, n))
        fnode = {v: k for k, v in enumerate(free)}
        rows, b = [], []
        pos = {}
        for e, (u, v) in enumerate(self.edges):
            for node in (u, v):
                if node in fnode:
                    pos.setdefault((fnode[node], e), (u, v))
        Aeq = np.zeros((2 * len(free) + 1, len(self.edges) + 1))
        for (r, e), (u, v) in pos.items():
            zu = self._z(u); zv = self._z(v)
            # force on node = sum alpha_e (z_other - z_node)
            other = zv if u != self._node_of(r) else zu
            if u in fnode and fnode[u] == r:
                d = (zu[0] - zv[0], zu[1] - zv[1])
            else:
                d = (zv[0] - zu[0], zv[1] - zu[1])
            Aeq[2 * r, e] = float(d[0]); Aeq[2 * r + 1, e] = float(d[1])
        Aeq[-1, :len(self.edges)] = 1.0
        beq = np.zeros(2 * len(free) + 1); beq[-1] = 1.0
        # t <= alpha_e  =>  t - alpha_e <= 0
        A_ub = np.zeros((len(self.edges), len(self.edges) + 1))
        for e in range(len(self.edges)):
            A_ub[e, e] = -1.0; A_ub[e, -1] = 1.0
        b_ub = np.zeros(len(self.edges))
        from scipy.optimize import linprog
        c = np.zeros(len(self.edges) + 1); c[-1] = -1.0
        res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=Aeq, b_eq=beq,
                      bounds=[(0, None)] * len(self.edges) + [(None, None)], method='highs')
        if not res.success:
            return None, res.message
        alpha = res.x[:len(self.edges)]
        return alpha, res.x[-1]

    def _node_of(self, r):
        return self.na + r

    def _z(self, node):
        if node < self.na:
            return self.A[node]
        if node < self.na + self.ns:
            return self.S[node - self.na]
        return self.Wpos[node - self.na - self.ns]

    # -------------------------------------------------- Schur + M
    def schur(self, alpha):
        n = self.na + self.ns + self.nf
        L = [[mp.mpf(0)] * n for _ in range(n)]
        for e, (u, v) in enumerate(self.edges):
            w = mp.mpf(float(alpha[e]))
            L[u][u] += w; L[v][v] += w; L[u][v] -= w; L[v][u] -= w
        order = list(range(self.na, n))
        for ii, k in enumerate(order):
            p = L[k][k]
            assert p > 0, ('nonpositive Dirichlet pivot', k, p)
            remain = order[ii + 1:] + list(range(self.na))
            for ix_i, i in enumerate(remain):
                if L[i][k] == 0:
                    continue
                for j in remain[ix_i:]:
                    val = L[i][j] - L[i][k] * L[k][j] / p
                    L[i][j] = val
                    if j != i:
                        L[j][i] = val
        q = {}
        for i in range(self.na):
            for j in range(i + 1, self.na):
                q[i, j] = -L[i][j]
        return q

    def M_from_q_and_labels(self, q, c_by_d, label_dist):
        na = self.na
        M = [[mp.mpf(0)] * na for _ in range(na)]
        neg = []
        for (i, j), qq in q.items():
            d = label_dist(i, j)
            c = c_by_d[d]
            if c is None:
                neg.append((i, j, d, float(qq)))
                continue
            v = 2 * qq * mp.mpf(c if isinstance(c, F) else float(c))
            M[i][i] += v; M[j][j] += v; M[i][j] -= v; M[j][i] -= v
        return M, neg


def eig_1perp(M):
    """eigenvalues of M, and of M restricted to 1^perp (Gram in basis e_0 - e_k)."""
    na = len(M)
    Mm = mp.matrix(na, na)
    for i in range(na):
        for j in range(na):
            Mm[i, j] = M[i][j]
    ev = mp.eigsy(Mm, eigvals_only=True)
    G = mp.matrix(na - 1, na - 1)
    for k in range(1, na):
        for l in range(1, na):
            G[k - 1, l - 1] = M[0][0] - M[0][l] - M[k][0] + M[k][l]
    gv = mp.eigsy(G, eigvals_only=True)
    return [float(v) for v in ev], [float(v) for v in gv], float(gv[0])
