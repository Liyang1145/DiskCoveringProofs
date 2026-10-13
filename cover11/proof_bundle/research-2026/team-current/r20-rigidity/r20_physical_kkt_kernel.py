"""r20-rigidity (step 14, anti block): PHYSICAL 18-branch architecture with finite-formula
gradients/Hessians, KKT common-active-gradient kernel, reflection block decomposition
(mixed block exactly 0), the ANTI 8x11 rank / rotation-quotient Hessian block, and the
KKT-kernel invariance (gauge + metric) lemmas.

Scope split (lead message 2026-09-25): the lead owns the SYMMETRIC 2x2 interval block
(free y0,y1 graph basis); this directory owns the ANTI 8x11 rank, the rotation quotient
3 -> 2, and the anti physical Hessian block.  Certified anti weights need r20-stress's
exact nu; all weights here are the numeric Danskin weight lambda in ker(J^T) cap simplex.

Anchor (read-only): ../lead/repaired_tc_krawczyk.json -- the 12D symmetric TC root box
(centre = exact binary64 rationals, radius 0x1.12e0be826d695p-30; Newton limit 62 digits).
Geometry root interface: lead/STRICT-EMPTY-FACET-COMPLETENESS.md.

No angle manifold: every branch is an explicit expression in the 22 centre coordinates and
is differentiated exactly by a second-order jet (no finite differences).  All the kernel /
block / identity statements below are evaluated at dps=60.

Writes r20_physical_kkt_kernel.json / .log.
"""
import json, itertools, time
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
LEAD = P.parent / 'lead'
DPS = 60
mp.mp.dps = DPS
N = 22                      # centre coordinates (11 sites x 2)
NC = 7                      # chart variables (a0..a3, y0, y1, R)
NB = 18                     # active branches
OUT = {}
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


# --------------------------------------------------------------------------- anchor
CERT = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
ROOT = [mp.mpf(s) for s in CERT['numeric_root']]
Z0 = ROOT[:NC]
LAM5 = ROOT[NC:]
RAD = float.fromhex(CERT['certificate']['radius_hex'])
CH = [float.fromhex(v) for v in CERT['certificate']['center_hex']]
R_STAR = Z0[6]
say('[S0] anchor: lead repaired TC root box, radius %.6e, contraction %s'
    % (RAD, CERT['certificate']['contraction_inf']))
say('     R* = %s' % mp.nstr(R_STAR, 42))
say('     box centre vs Newton limit: max |dCH| = %.3e' % max(abs(mp.mpf(CH[i]) - ROOT[i]) for i in range(NC)))

FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]
ACTIVE_FACES = list(range(9))
SLACK_FACES = [9, 10]
# reflection orbits of the 18 active branches (row indices in BR: 0..8 faces, 9..17 ties k=0..8)
FACE_ORBITS = [(0, 5), (1, 4), (2, 3), (6,), (7, 8)]
TIE_ORBITS = [(0, 7), (1, 6), (2, 5), (3, 4), (8,)]
PAIRED_FACE_REPS = [0, 1, 2, 7]
PAIRED_TIE_REPS = [0, 1, 2, 3]
FIXED_ROWS = [6, 17]                       # self-reflected fan (8,0,H1), self tie B_8


# --------------------------------------------------------------------------- jet
def SQ(x):
    if isinstance(x, Jet):
        return x._sqrt()
    return mp.sqrt(x)


class Jet(object):
    """value + gradient (n) + Hessian (n x n), truncated second-order Taylor arithmetic."""
    __slots__ = ('v', 'g', 'h', 'n')

    def __init__(self, v, g=None, h=None, n=N):
        self.v = v
        self.n = n
        self.g = g if g is not None else mp.zeros(n, 1)
        self.h = h if h is not None else mp.zeros(n, n)

    @staticmethod
    def var(i, v, n=N):
        g = mp.zeros(n, 1)
        g[i] = 1
        return Jet(v, g, mp.zeros(n, n), n)

    @staticmethod
    def const(v, n=N):
        return Jet(mp.mpf(v), mp.zeros(n, 1), mp.zeros(n, n), n)

    def __add__(self, o):
        o = _j(o, self.n)
        return Jet(self.v + o.v, self.g + o.g, self.h + o.h, self.n)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.g, -self.h, self.n)

    def __sub__(self, o):
        return self + (-_j(o, self.n))

    def __rsub__(self, o):
        return _j(o, self.n) + (-self)

    def __mul__(self, o):
        o = _j(o, self.n)
        return Jet(self.v * o.v, self.v * o.g + o.v * self.g,
                   self.v * o.h + o.v * self.h + self.g * o.g.T + o.g * self.g.T, self.n)

    __rmul__ = __mul__

    def __truediv__(self, o):
        return self * _j(o, self.n)._recip()

    def __rtruediv__(self, o):
        return _j(o, self.n) * self._recip()

    def __pow__(self, k):
        if k == 1:
            return self
        if k == 2:
            return self * self
        r = Jet.const(1, self.n)
        for _ in range(k):
            r = r * self
        return r

    def _recip(self):
        r = 1 / self.v
        return Jet(r, -self.g * r * r,
                   mp.mpf(2) * r ** 3 * (self.g * self.g.T) - r * r * self.h, self.n)

    def _sqrt(self):
        s = mp.sqrt(self.v)
        return Jet(s, self.g / (2 * s),
                   self.h / (2 * s) - (self.g * self.g.T) / (4 * s ** 3), self.n)

    def _cos(self):
        return Jet(mp.cos(self.v), -mp.sin(self.v) * self.g,
                   -mp.cos(self.v) * (self.g * self.g.T) - mp.sin(self.v) * self.h, self.n)

    def _sin(self):
        return Jet(mp.sin(self.v), mp.cos(self.v) * self.g,
                   -mp.sin(self.v) * (self.g * self.g.T) + mp.cos(self.v) * self.h, self.n)


def _j(x, n=N):
    return x if isinstance(x, Jet) else Jet.const(mp.mpf(x), n)


def jcos(u):
    return _j(u)._cos()


def jsin(u):
    return _j(u)._sin()


# --------------------------------------------------------------------------- branches
def face_branch(S, tri):
    """circumcentre/circumradius of a noncollinear triple (explicit Cramer formula)."""
    a, b, c = tri
    ca, cb, cc = S[a], S[b], S[c]
    g1x, g1y = ca[0] - cb[0], ca[1] - cb[1]
    g2x, g2y = ca[0] - cc[0], ca[1] - cc[1]
    det = g1x * g2y - g1y * g2x
    b1 = -(g1x * g1x + g1y * g1y) / 2
    b2 = -(g2x * g2x + g2y * g2y) / 2
    wx = (b1 * g2y - b2 * g1y) / det
    wy = (g1x * b2 - g2x * b1) / det
    return (ca[0] + wx, ca[1] + wy), SQ(wx * wx + wy * wy)


def tie_branch(S, k, sgn):
    """p = perpendicular bisector of (C_k, C_{k+1}) intersected with the unit circle (sign sgn);
    f = |p - C_k| (boundary-tie covering-radius branch)."""
    ca, cb = S[k], S[(k + 1) % 9]
    dx, dy = cb[0] - ca[0], cb[1] - ca[1]
    D = dx * dx + dy * dy
    kap = ((cb[0] * cb[0] + cb[1] * cb[1]) - (ca[0] * ca[0] + ca[1] * ca[1])) / 2
    dl = SQ(D)
    a0x, a0y = (kap / D) * dx, (kap / D) * dy
    t = sgn * SQ(1 - (a0x * a0x + a0y * a0y))
    p = (a0x + t * (-dy / dl), a0y + t * (dx / dl))
    wx, wy = p[0] - ca[0], p[1] - ca[1]
    return p, SQ(wx * wx + wy * wy)


def vval(x):
    return x.v if isinstance(x, Jet) else x


def chord_inner_pin(S, R, tri):
    """U = intersection of the radius-R circles around S[tri[0]], S[tri[1]] on the side of
    S[tri[2]] (the chord-circle inner pin); returns (|U - c| - R, U)."""
    a, b, c = tri
    ca, cb, cc = S[a], S[b], S[c]
    dx, dy = cb[0] - ca[0], cb[1] - ca[1]
    D = dx * dx + dy * dy
    dl = SQ(D)
    mx, my = (ca[0] + cb[0]) / 2, (ca[1] + cb[1]) / 2
    t = SQ(R * R - D / 4)
    u1 = (mx + t * (-dy / dl), my + t * (dx / dl))
    u2 = (mx - t * (-dy / dl), my - t * (dx / dl))
    d1 = (u1[0] - cc[0]) ** 2 + (u1[1] - cc[1]) ** 2
    d2 = (u2[0] - cc[0]) ** 2 + (u2[1] - cc[1]) ** 2
    u = u1 if vval(d1) < vval(d2) else u2
    return SQ((u[0] - cc[0]) ** 2 + (u[1] - cc[1]) ** 2) - R, u


def chart_sites_f(z):
    """lead TC chart z=(a0..a3,y0,y1,R) -> 11 sites C0..C8, H0, H1 (source identity:
    lead/TC-ROOT-SOURCE-IDENTITY.md; conventions as r20_tc_root_independent.py)."""
    a0, a1, a2, a3, y0, y1, R = z
    a4 = mp.pi - 2 * (a0 + a1 + a2 + a3)
    ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    th = [mp.mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + ak[k - 1] + ak[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (ak[k] + ak[k + 1])
    rho = [mp.cos(ak[k]) - mp.sqrt(R * R - mp.sin(ak[k]) ** 2) for k in range(9)]
    C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
    return C + [(y0, mp.mpf(0)), (y1, mp.mpf(0))], ak, th, rho


def chart_sites_jet(z):
    a0, a1, a2, a3, y0, y1, R = z
    a4 = mp.pi - 2 * (a0 + a1 + a2 + a3)
    ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    th = [Jet.const(0, NC)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + ak[k - 1] + ak[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (ak[k] + ak[k + 1])
    rho = [jcos(ak[k]) - SQ(R * R - jsin(ak[k]) ** 2) for k in range(9)]
    C = [(rho[k] * jcos(th[k]), rho[k] * jsin(th[k])) for k in range(9)]
    return C + [(y0, Jet.const(0, NC)), (y1, Jet.const(0, NC))], ak, th, rho


SITES, AK, TH, RHO = chart_sites_f(Z0)
X0 = [v for s in SITES for v in s]
BK = [(mp.cos(TH[k] + AK[k]), mp.sin(TH[k] + AK[k])) for k in range(9)]
M_C = (Z0[4] + Z0[5]) / 2
H_C = mp.sqrt(R_STAR ** 2 - ((Z0[5] - Z0[4]) / 2) ** 2)
say('[S1] chart image: rho in [%s, %s]; hubs y0=%s y1=%s'
    % (mp.nstr(min(RHO), 18), mp.nstr(max(RHO), 18), mp.nstr(Z0[4], 20), mp.nstr(Z0[5], 20)))


def all_branches(S):
    F = {}
    for i, tri in enumerate(FACES):
        F[('face', i)] = face_branch(S, tri)
    for k in range(9):
        for sgn in (1, -1):
            F[('tie', k, sgn)] = tie_branch(S, k, sgn)
    return F


VAL = all_branches(SITES)
fat = [VAL[('face', i)][1] - R_STAR for i in ACTIVE_FACES]
fsl = [R_STAR - VAL[('face', i)][1] for i in SLACK_FACES]
say('\n[S2] branch values: active faces max |f-R*| = %.2e ; slack R*-f in [%s, %s]'
    % (max(abs(x) for x in fat), mp.nstr(min(fsl), 10), mp.nstr(max(fsl), 10)))

TIEPICK = {}
dis = []
for k in range(9):
    cands = []
    for sgn in (1, -1):
        p, f = VAL[('tie', k, sgn)]
        ds = sorted((mp.sqrt((p[0] - s[0]) ** 2 + (p[1] - s[1]) ** 2), i) for i, s in enumerate(SITES))
        ok = set(i for _, i in ds[:2]) == {k, (k + 1) % 9}
        cands.append((sgn, f, ok, mp.sqrt(p[0] ** 2 + p[1] ** 2)))
    good = [c for c in cands if c[2]]
    TIEPICK[k] = good[0][0] if len(good) == 1 else min(cands, key=lambda c: c[1])[0]
    dis.append((k, TIEPICK[k], cands))
tie_dev = [abs(VAL[('tie', k, TIEPICK[k])][1] - R_STAR) for k in range(9)]
for k, sgn, cands in dis:
    if k in (0, 1, 8):
        p, f = VAL[('tie', k, sgn)]
        other = [c for c in cands if c[0] != sgn][0]
        say('     tie %d: sign %+d f-R* = %+.1e |p|-1 = %.1e (far branch f-R* = %+.3f)'
            % (k, sgn, float(f - R_STAR), float(mp.sqrt(p[0] ** 2 + p[1] ** 2) - 1), float(other[1] - R_STAR)))
say('     all 9 ties: max |f - R*| = %.2e (boundary ties are saturated identically in the chart)'
    % max(tie_dev))

dpin = max(float(mp.sqrt((VAL[('face', i)][0][0] - (SITES[FACES[i][0]][0] + SITES[FACES[i][1]][0] - BK[FACES[i][0]][0])) ** 2
                    + (VAL[('face', i)][0][1] - (SITES[FACES[i][0]][1] + SITES[FACES[i][1]][1] - BK[FACES[i][0]][1])) ** 2))
           for i in range(7))
dtie = max(float(mp.sqrt((VAL[('tie', k, TIEPICK[k])][0][0] - BK[k][0]) ** 2
                         + (VAL[('tie', k, TIEPICK[k])][0][1] - BK[k][1]) ** 2)) for k in range(9))
dcen = max(min(float(mp.sqrt((VAL[('face', i)][0][0] - M_C) ** 2 + (VAL[('face', i)][0][1] - sg * H_C) ** 2))
               for sg in (1, -1)) for i in (7, 8))
say('     chart coincidence: fans vs pins U_k %.1e ; ties vs B_k %.1e ; central vs (m,+-h) %.1e'
    % (dpin, dtie, dcen))


def critical_set(S):
    """numeric cross-check of the branch catalogue (root interface = the lead's strict-empty
    facet lemma; this only calibrates the instrument)."""
    crit = []
    for tri in itertools.combinations(range(11), 3):
        ca, cb, cc = S[tri[0]], S[tri[1]], S[tri[2]]
        if (cb[0] - ca[0]) * (cc[1] - ca[1]) - (cb[1] - ca[1]) * (cc[0] - ca[0]) == 0:
            continue                                       # (C4,H0,H1) is exactly collinear
        p, f = face_branch(S, tri)
        if p[0] ** 2 + p[1] ** 2 > 1:
            continue
        ds = sorted((mp.sqrt((p[0] - s[0]) ** 2 + (p[1] - s[1]) ** 2), i) for i, s in enumerate(S))
        if set(i for _, i in ds[:3]) == set(tri):
            crit.append(('V3', tri, f))
    for k in range(9):
        p, f = tie_branch(S, k, TIEPICK[k])
        ds = sorted((mp.sqrt((p[0] - s[0]) ** 2 + (p[1] - s[1]) ** 2), q) for q, s in enumerate(S))
        if set(q for _, q in ds[:2]) == {k, (k + 1) % 9}:
            crit.append(('V2b', k, f))
    return crit


CRIT = critical_set(SITES)
tight = [c for c in CRIT if c[2] > R_STAR - mp.mpf('1e-12')]
say('     critical-set cross-check: %d points, %d at radius R* (expect 20, 18)' % (len(CRIT), len(tight)))

# --------------------------------------------------------------------------- jets
say('\n[S3] exact jet derivatives of the 18 active branches (no finite differences)')
t0 = time.time()
SJ = [(Jet.var(2 * i, X0[2 * i]), Jet.var(2 * i + 1, X0[2 * i + 1])) for i in range(11)]
BR = []
for i in ACTIVE_FACES:
    BR.append(('face', FACES[i], face_branch(SJ, FACES[i])))
for k in range(9):
    BR.append(('tie', (k, (k + 1) % 9), tie_branch(SJ, k, TIEPICK[k])))
Jm = mp.matrix(NB, N)
Hm = [mp.matrix(N, N) for _ in range(NB)]
for r, (kind, lab, (p, f)) in enumerate(BR):
    assert abs(f.v - R_STAR) < mp.mpf('1e-40'), (kind, lab, f.v - R_STAR)
    for a in range(N):
        Jm[r, a] = f.g[a]
        for b in range(N):
            Hm[r][a, b] = f.h[a, b]
say('     jet time %.1fs ; max |f - R*| = %.2e' % (time.time() - t0, max(abs(mp.mpf(f.v) - R_STAR) for _, _, (p, f) in BR)))
Jf = np.array([[float(Jm[r, a]) for a in range(N)] for r in range(NB)])
Hf = np.array([[[float(Hm[r][a, b]) for b in range(N)] for a in range(N)] for r in range(NB)])


def branch_value(kind, lab, x):
    S = [(mp.mpf(x[2 * i]), mp.mpf(x[2 * i + 1])) for i in range(11)]
    return face_branch(S, lab)[1] if kind == 'face' else tie_branch(S, lab[0], TIEPICK[lab[0]])[1]


HD = mp.mpf('1e-15')
ctrl = []
for r, (kind, lab, (p, f)) in enumerate(BR[:6]):
    for a in (0, 5, 13):
        xp = list(X0); xm = list(X0)
        xp[a] += HD; xm[a] -= HD
        d = (branch_value(kind, lab, xp) - branch_value(kind, lab, xm)) / (2 * HD)
        ctrl.append(float(abs(d - mp.mpf(Jm[r, a]))))
say('     FD control (6 branches x 3 coords): max |FD - jet| = %.2e' % max(ctrl))

# --------------------------------------------------------------------------- reflection bases (exact, mpmath)
s2 = 1 / mp.sqrt(2)
BSm = mp.zeros(N, 11)
BAm = mp.zeros(N, 11)
col = 0
for k in range(4):
    j = 8 - k
    for t in range(2):
        sg = mp.mpf(1) if t == 0 else mp.mpf(-1)      # y flips under x -> x
        BSm[2 * k + t, col] = s2; BSm[2 * j + t, col] = sg * s2
        BAm[2 * k + t, col] = s2; BAm[2 * j + t, col] = -sg * s2
        col += 1
BSm[2 * 4, col] = 1; BAm[2 * 4 + 1, col] = 1; col += 1
BSm[2 * 9, col] = 1; BAm[2 * 9 + 1, col] = 1; col += 1
BSm[2 * 10, col] = 1; BAm[2 * 10 + 1, col] = 1; col += 1
assert col == 11
SIGm = BSm * BSm.T - BAm * BAm.T
rot_m = mp.matrix([x for i in range(11) for x in (-X0[2 * i + 1], X0[2 * i])])
rot_m = rot_m / mp.sqrt(sum(x * x for x in rot_m))
say('\n[S4] reflection: Sym 11D, Anti 11D (exact bases)')
say('     |P_Sym rot| = %.1e ; |P_Anti rot| = %.1e ; max |J rot| = %.1e (equivariance)'
    % (mp.sqrt(sum(x * x for x in (BSm.T * rot_m))), mp.sqrt(sum(x * x for x in (BAm.T * rot_m))),
       max(abs(x) for x in (Jm * rot_m))))
show = max(abs(x) for x in (SIGm * SIGm - mp.eye(N)))
say('     reflection involution check |SIG^2 - I| = %.1e' % show)

# --------------------------------------------------------------------------- gradient maps + anti 8x11
Js = Jm * BSm
Ja = Jm * BAm
_, Ss, _ = mp.svd_r(Js)
_, Sa, _ = mp.svd_r(Ja)
rank_s = sum(1 for x in Ss if x > mp.mpf('1e-8') * Ss[0])
rank_a = sum(1 for x in Sa if x > mp.mpf('1e-8') * Sa[0])
say('\n[S5] gradient maps')
say('     sv(J|Sym) = ' + ' '.join('%.4f' % x for x in Ss))
say('     sv(J|Anti)= ' + ' '.join('%.4f' % x for x in Sa))
say('     rank(J|Sym) = %d  rank(J|Anti) = %d ; gaps %.1e / %.1e'
    % (rank_s, rank_a, Ss[rank_s - 1] / Ss[rank_s], Sa[rank_a - 1] / Sa[rank_a]))


def null_from_minor(M, piv_cols):
    """exact null space of an m x n matrix given m independent pivot columns (mpmath)."""
    m, n = M.rows, M.cols
    free = [j for j in range(n) if j not in piv_cols]
    Mp = mp.matrix(m, m)
    for i in range(m):
        for jj, j in enumerate(piv_cols):
            Mp[i, jj] = M[i, j]
    out = []
    for fc in free:
        rhs = mp.matrix([M[i, fc] for i in range(m)])
        sol = mp.lu_solve(Mp, rhs)
        v = mp.matrix(n, 1)
        v[fc] = 1
        for jj, j in enumerate(piv_cols):
            v[j] = -sol[jj]
        out.append(v)
    return out


def pick_independent(Mnp, k, rows=True, tol=1e-7):
    """greedy selection of k independent rows (or columns) of a float64 matrix."""
    idx, out = (list(range(Mnp.shape[0])), []) if rows else (list(range(Mnp.shape[1])), [])
    for i in idx:
        cand = out + [i]
        sub = Mnp[cand, :] if rows else Mnp[:, cand]
        if np.linalg.matrix_rank(sub, tol=tol) > len(out):
            out.append(i)
        if len(out) == k:
            break
    return out


# anti representative 8x11 block: one row per paired orbit
anti_rows = PAIRED_FACE_REPS + [9 + k for k in PAIRED_TIE_REPS]
Am_np = Jf[anti_rows, :]
rows8 = pick_independent(Am_np, 8, rows=True)
A8 = mp.matrix(8, 11)
Ja_mp = Jm * BAm
for i, r in enumerate(rows8):
    for j in range(11):
        A8[i, j] = Ja_mp[anti_rows[r], j]
# best (largest |det|) 8x8 pivot minor, chosen in float64 then evaluated in dps precision
A8_np = np.array([[float(A8[i, j]) for j in range(11)] for i in range(8)])
best_det, best_cols = -1.0, None
for cc_ in itertools.combinations(range(11), 8):
    d_ = abs(np.linalg.det(A8_np[:, list(cc_)]))
    if d_ > best_det:
        best_det, best_cols = d_, cc_
cols8 = list(best_cols)
minor8 = mp.matrix(8, 8)
for i in range(8):
    for j in range(8):
        minor8[i, j] = A8[i, cols8[j]]
det8 = mp.det(minor8)
say('     anti 8x11 rows (orbit reps) %s -> used rows %s ; best pivot cols %s'
    % (anti_rows, rows8, cols8))
_, S8, V8 = mp.svd_r(A8)
say('     sv(A_anti 8x11) = ' + ' '.join('%.4f' % x for x in S8) + ' ; rank 8')
say('     pivot minor det = %s (float64 best %.3e)' % (mp.nstr(det8, 12), best_det))
KA11_minor = null_from_minor(A8, cols8)                 # 3 kernel vectors in the 11D anti coords
res_k = max(abs(x) for v in KA11_minor for x in (A8 * v))
# independent route: mpmath SVD of J|Anti (18x11) -> rows 8..10 of V are the right singular vectors
_, Sa_, Va = mp.svd_r(Ja)
KA11_svd = [mp.matrix([Va[r, j] for j in range(11)]) for r in range(8, 11)]
res_k_svd = max(abs(x) for v in KA11_svd for x in (Jm * BAm * v))
# agreement of the two routes (same 3D subspace)
Gm = mp.matrix(11, 6)
for i in range(11):
    for j in range(3):
        Gm[i, j] = KA11_minor[j][i]
        Gm[i, 3 + j] = KA11_svd[j][i]
sv_mix = mp.svd_r(Gm)[1]
rank_mix = sum(1 for x in sv_mix if x > mp.mpf('1e-8') * sv_mix[0])
say('     kernel of A_anti: dim 3 ; max |A_anti k| = %.1e ; SVD route residual %.1e ; rank(minor+SVD basis) = %d (3 expected)'
    % (res_k, res_k_svd, rank_mix))
KA11 = KA11_svd
rot_a = BAm.T * rot_m
res_rot = max(abs(x) for x in (A8 * rot_a))
Gm3 = mp.matrix(11, 3)
for i in range(11):
    for j in range(3):
        Gm3[i, j] = KA11[j][i]
AtA = Gm3.T * Gm3
coef = mp.lu_solve(AtA, Gm3.T * rot_a)
fit = max(abs(x) for x in (Gm3 * coef - rot_a))
say('     |A_anti rot_a| = %.1e ; rotation inside span(kernel): fit residual %.1e' % (res_rot, fit))
KA22 = [BAm * v for v in KA11]
KA22 = [v / mp.sqrt(sum(x * x for x in v)) for v in KA22]
# orthonormal basis of the full 3D anti kernel (rotation included) and of the 2D quotient
K3 = []
for v in KA22:
    w = v
    for c in K3:
        w = w - sum(x * y for x, y in zip(w, c)) * c
    nw = mp.sqrt(sum(x * x for x in w))
    if nw > mp.mpf('1e-12'):
        K3.append(w / nw)
KS_ = []
for v in K3:
    w = v - sum(x * y for x, y in zip(v, rot_m)) * rot_m
    for c in KS_:
        w = w - sum(x * y for x, y in zip(w, c)) * c
    nw = mp.sqrt(sum(x * x for x in w))
    if nw > mp.mpf('1e-12'):
        KS_.append(w / nw)
say('     anti kernel orthonormal basis dim %d (rotation + quotient %d)' % (len(K3), len(KS_)))
# sym kernel via mpmath SVD of J|Sym (18x11): rows 9,10 of V
_, Ss_, Vs = mp.svd_r(Js)
KS11 = [mp.matrix([Vs[r, j] for j in range(11)]) for r in range(rank_s, 11)]
KS22 = [BSm * v for v in KS11]
KS22 = [v / mp.sqrt(sum(x * x for x in v)) for v in KS22]
res_ksym = max(abs(x) for v in KS11 for x in (Js * v))
say('     sym kernel: dim %d ; max |J|Sym k| = %.1e (lead owns the interval block)' % (len(KS22), res_ksym))

# --------------------------------------------------------------------------- lambda + blocks
U, SJ_, V = mp.svd_r(Jm)
u0 = mp.matrix([U[i, NB - 1] for i in range(NB)])
JJ = Jm * Jm.T
Br = mp.matrix(NB + 1, NB + 1)
for i in range(NB):
    for j in range(NB):
        Br[i, j] = JJ[i, j]
for i in range(NB):
    Br[i, NB] = u0[i]
    Br[NB, i] = u0[i]
rhs = mp.matrix(NB + 1, 1)
rhs[NB] = 1
sol = mp.lu_solve(Br, rhs)
lam = [sol[i] for i in range(NB)]
lam = [x / sum(lam) for x in lam]
say('\n[S6] Danskin weight lambda in ker(J^T) cap simplex (numeric; certified version needs stress nu)')
say('     lam min %.6e max %.6e sum %.15f' % (min(lam), max(lam), sum(lam)))
resL = max(abs(sum(lam[i] * Jm[i, a] for i in range(NB))) for a in range(N))
say('     max |sum lam_i grad f_i| at dps=%d: %.1e' % (DPS, resL))
lam_sym = max([abs(lam[o[0]] - lam[o[1]]) for o in FACE_ORBITS if len(o) == 2]
              + [abs(lam[9 + o[0]] - lam[9 + o[1]]) for o in TIE_ORBITS if len(o) == 2])
say('     reflection invariance |lam_r - lam_sigma(r)| = %.1e (premise of the exact 0 mixed block)' % lam_sym)


def orbit_val(o, base=0):
    return sum(lam[base + i] for i in o) / len(o)


say('     orbit weights: faces ' + ' '.join('%.6f' % orbit_val(o) for o in FACE_ORBITS)
    + ' ; ties ' + ' '.join('%.6f' % orbit_val(o, 9) for o in TIE_ORBITS))

HW = mp.zeros(N, N)
for i in range(NB):
    HW = HW + lam[i] * Hm[i]
HW = (HW + HW.T) / 2
mixed = BSm.T * HW * BAm
say('     mixed block Sym x Anti: max |BS^T HW BA| = %.1e  (EXACT 0 by invariance, not ignored)'
    % max(abs(x) for x in mixed))
say('     commutator |SIG HW - HW SIG| = %.1e' % max(abs(x) for x in (SIGm * HW - HW * SIGm)))
hwr = HW * rot_m
say('     rotation is an exact kernel direction of HW: |HW rot| = %.1e ; rot^T HW rot = %.1e'
    % (max(abs(x) for x in hwr), (rot_m.T * HW * rot_m)[0]))
KA3 = mp.matrix(N, 3)
for j in range(3):
    for i in range(N):
        KA3[i, j] = K3[j][i]
B3 = KA3.T * HW * KA3
ev3, _ = mp.eigsy(B3)
say('     anti block 3x3 eigenvalues (physical metric, orthonormal basis) = ' + ' '.join('%.10f' % x for x in ev3))
KQ = mp.matrix(N, len(KS_))
for j in range(len(KS_)):
    for i in range(N):
        KQ[i, j] = KS_[j][i]
B2 = KQ.T * HW * KQ
ev2, _ = mp.eigsy(B2)
say('     anti quotient 2x2 eigenvalues = ' + ' '.join('%.10f' % x for x in ev2))
KS_m = mp.matrix(N, len(KS22))
for j in range(len(KS22)):
    for i in range(N):
        KS_m[i, j] = KS22[j][i]
B2s = KS_m.T * HW * KS_m
ev2s, _ = mp.eigsy(B2s)
say('     sym 2x2 eigenvalues (physical metric; lead owns interval version) = ' + ' '.join('%.10f' % x for x in ev2s))

# max-form diagnostics (float64, necessary-condition side)
from scipy.optimize import minimize as spmin
Q2 = np.array([[float(KS_[j][i]) for i in range(N)] for j in range(len(KS_))])
Ai_anti = np.einsum('pa,iab,qb->ipq', Q2, Hf, Q2)
rng = np.random.default_rng(3)
best_val, best_v = -1e9, None
for it in range(4000):
    z = rng.normal(size=len(KS_)); z /= np.linalg.norm(z)
    val = float(np.einsum('p,ipq,q->i', z, Ai_anti, z).max())
    if val > best_val:
        best_v, best_val = z.copy(), val
for kick in range(4):
    z0 = best_v if kick == 0 else best_v + 0.4 * rng.normal(size=len(KS_))
    o = spmin(lambda z: float(np.einsum('p,ipq,q->i', z / np.linalg.norm(z), Ai_anti, z / np.linalg.norm(z)).max()),
              z0 / np.linalg.norm(z0), method='Nelder-Mead', options={'maxiter': 8000})
    if o.fun < best_val:
        best_val = float(o.fun)
say('     anti max-form value min_v max_i v^T H_i v (mod rotation, float64) = %.8f (>= 0 required)' % best_val)

# --------------------------------------------------------------------------- gauge conversion (fan face)
say('\n[S7] gauge conversion: radius excess G = kappa * (pin residual f), fan face (2,3,H0)')
tri = FACES[1]
pin0, up = chord_inner_pin(SITES, R_STAR, tri)
fex0 = VAL[('face', 1)][1] - R_STAR
say('     at the root: pin residual %+.1e ; face excess %+.1e' % (float(pin0), float(fex0)))
cA, cB, cC = SITES[tri[0]], SITES[tri[1]], SITES[tri[2]]
chx, chy = cB[0] - cA[0], cB[1] - cA[1]
chl = mp.sqrt(chx * chx + chy * chy)
y_sig = ((cC[0] - cA[0]) * chy - (cC[1] - cA[1]) * chx) / chl
u_out = (cA[0] + cB[0] - up[0], cA[1] + cB[1] - up[1])
Fout = (cC[0] - u_out[0]) ** 2 + (cC[1] - u_out[1]) ** 2 - R_STAR ** 2
kap = Fout / (4 * y_sig ** 2)
say('     conversion factor kappa = Fout/(4y^2) = %s  (Fout = %s, y = %s)'
    % (mp.nstr(kap, 18), mp.nstr(Fout, 14), mp.nstr(y_sig, 14)))


def G_and_f(x, R):
    S = [(mp.mpf(x[2 * i]), mp.mpf(x[2 * i + 1])) for i in range(11)]
    return chord_inner_pin(S, mp.mpf(R), tri)[0], face_branch(S, tri)[1] - mp.mpf(R)


dirv = np.zeros(N)
dirv[2 * tri[0]] = 1.0
dirv[2 * tri[1] + 1] = -1.0
for t in (mp.mpf('1e-6'), mp.mpf('1e-9')):
    xp = [mp.mpf(X0[i]) + t * mp.mpf(dirv[i]) for i in range(N)]
    Gp1, fp1 = G_and_f(xp, R_STAR)
    say('     t=%.0e: face excess / pin residual = %s (converging to kappa)' % (t, mp.nstr(fp1 / Gp1, 16)))


def sealed2(fun, x0, v, h=mp.mpf('1e-8')):
    return (fun([x0[i] + h * v[i] for i in range(N)]) - 2 * fun(x0)
            + fun([x0[i] - h * v[i] for i in range(N)])) / (h * h)


v1 = [mp.mpf(x) for x in (dirv / np.linalg.norm(dirv))]
d2_pin = sealed2(lambda x: G_and_f(x, R_STAR)[0], X0, v1)
d2_fex = sealed2(lambda x: G_and_f(x, R_STAR)[1], X0, v1)
say('     full space (transverse direction): d2(face excess) = %s ; kappa*d2(pin residual) = %s'
    % (mp.nstr(d2_fex, 14), mp.nstr(kap * d2_pin, 14)))
say('     -> |difference| = %.2e : the df x dkappa cross terms do NOT vanish off the kernel'
    % float(abs(d2_fex - kap * d2_pin)))

# jet version of both functions (R fixed at R*) and the kernel identity
SJ2 = [(Jet.var(2 * i, X0[2 * i]), Jet.var(2 * i + 1, X0[2 * i + 1])) for i in range(11)]
pJ, uJ = chord_inner_pin(SJ2, Jet.const(R_STAR), tri)
fJ = face_branch(SJ2, tri)[1] - Jet.const(R_STAR)


def quad(f, v):
    return sum(v[a] * v[b] * f.h[a, b] for a in range(N) for b in range(N))


rows = []
for j in range(len(KS_)):
    vv = [KS_[j][i] for i in range(N)]
    rows.append((mp.nstr(quad(fJ, vv), 14), mp.nstr(kap * quad(pJ, vv), 14),
                 mp.nstr(abs(quad(fJ, vv) - kap * quad(pJ, vv)), 3)))
say('     kernel directions (d2 face excess, kappa*d2 pin residual, |diff|): ' + ' ; '.join('(%s, %s, %s)' % t for t in rows))

# --------------------------------------------------------------------------- interface calibration
say('\n[S7b] interface calibration: does lambda factorize as (orbit multiplier) x (branch factor)?')
face_c = []
for i in ACTIVE_FACES:
    tr = FACES[i]
    cA, cB, cC = SITES[tr[0]], SITES[tr[1]], SITES[tr[2]]
    _, up_i = chord_inner_pin(SITES, R_STAR, tr)
    u_out = (cA[0] + cB[0] - up_i[0], cA[1] + cB[1] - up_i[1])
    Fout_i = (cC[0] - u_out[0]) ** 2 + (cC[1] - u_out[1]) ** 2 - R_STAR ** 2
    chx, chy = cB[0] - cA[0], cB[1] - cA[1]
    chl = mp.sqrt(chx * chx + chy * chy)
    y_i = ((cC[0] - cA[0]) * chy - (cC[1] - cA[1]) * chx) / chl
    face_c.append(4 * y_i ** 2 / Fout_i)
tie_b = [R_STAR / (RHO[k] * mp.sin(AK[k])) + R_STAR / (RHO[(k + 1) % 9] * mp.sin(AK[(k + 1) % 9])) for k in range(9)]
spread_f = max((max(lam[i] * face_c[i] for i in o) - min(lam[i] * face_c[i] for i in o)) for o in FACE_ORBITS)
spread_t = max((max(lam[9 + j] * tie_b[j] for j in o) - min(lam[9 + j] * tie_b[j] for j in o)) for o in TIE_ORBITS)
say('     face factors c_i = 4y_i^2/Fout_i : ' + ' '.join('%.6f' % x for x in face_c))
say('     tie  factors b_j = a_{j,R}+a_{j+1,R}: ' + ' '.join('%.6f' % x for x in tie_b))
say('     orbit-constant product w_i*c_i: spread %.2e (faces) ; w_j*b_j: spread %.2e (ties)'
    % (float(spread_f), float(spread_t)))
say('     implied orbit multipliers mu_k = w_i c_i : ' + ' '.join('%.8f' % (lam[o[0]] * face_c[o[0]]) for o in FACE_ORBITS))
say('     implied orbit multipliers nu_j = w_j b_j : ' + ' '.join('%.8f' % (lam[9 + o[0]] * tie_b[o[0]]) for o in TIE_ORBITS))

# --------------------------------------------------------------------------- metric / congruence
say('\n[S8] metric / congruence transfer (weighted form in two charts)')
zJ = [Jet.var(i, Z0[i], NC) for i in range(NC)]
SJ7, _, _, _ = chart_sites_jet(zJ)
Wj = None
for r, (kind, lab, (p, f)) in enumerate(BR):
    Wj = lam[r] * f if Wj is None else Wj + lam[r] * f
Wp = None
for r, (kind, lab, (p, f)) in enumerate(BR):
    fp = face_branch(SJ7, lab)[1] if kind == 'face' else tie_branch(SJ7, lab[0], TIEPICK[lab[0]])[1]
    Wp = lam[r] * fp if Wp is None else Wp + lam[r] * fp
say('     W = sum lam_i f_i : |grad_22D|_max = %.1e ; |grad_7D|_max = %.1e ; W - R* = %.1e'
    % (max(abs(Wj.g[i]) for i in range(N)), max(abs(Wp.g[i]) for i in range(NC)), float(Wp.v - R_STAR)))
Y = mp.matrix(N, NC)
for i in range(11):
    for t in range(2):
        for c in range(NC):
            Y[2 * i + t, c] = SJ7[i][t].g[c]
HW11 = BSm.T * HW * BSm
chap = mp.matrix(NC, NC)
for i in range(NC):
    for j in range(NC):
        chap[i, j] = Wp.h[i, j]
chap2 = Y.T * HW * Y
say('     pullback (7D jets) vs chain Y^T HW Y : max |diff| = %.1e (grad W = 0 kills chart curvature)'
    % max(abs(x) for x in (chap - chap2)))
# chart-metric generalized eigenvalues on the sym kernel
Ynp = np.array([[float(Y[i, c]) for c in range(NC)] for i in range(N)])
KSnp = np.array([[float(KS22[j][i]) for i in range(N)] for j in range(len(KS22))])
Vz = np.linalg.lstsq(Ynp, KSnp.T, rcond=None)[0]
say('     chart directions for the sym kernel: |Y Vz - KS| = %.1e' % np.abs(Ynp @ Vz - KSnp.T).max())
Gz = Vz.T @ Vz
chap_np = np.array([[float(chap[i, j]) for j in range(NC)] for i in range(NC)])
ev_z = __import__('scipy.linalg', fromlist=['eigh']).eigh(Vz.T @ chap_np @ Vz, Gz)[0]  # symmetric generalized solve
say('     sym 2x2 eigenvalues: physical metric %s ; chart z metric %s'
    % (' '.join('%.6f' % float(x) for x in ev2s), ' '.join('%.6f' % x for x in ev_z)))
say('     metric G_z eigenvalues %s ; per-mode ratios %.4f / %.4f (NOT equal -> eigenvalues are chart-dependent)'
    % (' '.join('%.6f' % x for x in np.linalg.eigvalsh(Gz)), ev_z[0] / float(ev2s[0]), ev_z[1] / float(ev2s[1])))
lam_raw = np.linalg.eigvalsh(np.array([[float(HW[i, j]) for j in range(N)] for i in range(N)]))
rng2 = np.random.default_rng(11)
Y0 = np.eye(N) + 0.35 * rng2.normal(size=(N, N))
HWnp = np.array([[float(HW[i, j]) for j in range(N)] for i in range(N)])
lam_con = np.linalg.eigvalsh(Y0.T @ HWnp @ Y0)
say('     controlled congruence (random linear chart): (pos, neg) inertia %s vs %s ; smallest three after change %s'
    % ((int((lam_raw > 1e-9).sum()), int((lam_raw < -1e-9).sum())),
       (int((lam_con > 1e-9).sum()), int((lam_con < -1e-9).sum())),
       ' '.join('%.4f' % x for x in lam_con[:3])))

# --------------------------------------------------------------------------- save
OUT.update({
    'anchor': {'file': '../lead/repaired_tc_krawczyk.json', 'box_radius_hex': CERT['certificate']['radius_hex'],
               'R_star': mp.nstr(R_STAR, 42), 'newton_trace': CERT['newton_trace']},
    'scope': 'physical 18-branch architecture + anti block; sym block owned by lead',
    'branch_values': {'active_face_max_abs_f_minus_R': float(max(abs(x) for x in fat)),
                      'slack_face_gaps': [float(x) for x in fsl],
                      'tie_max_abs_f_minus_R': float(max(tie_dev)),
                      'chart_coincidence': {'fans_vs_pins': dpin, 'ties_vs_Bk': dtie, 'central_vs_mh': dcen}},
    'critical_set_xcheck': {'count': len(CRIT), 'tight': len(tight)},
    'fd_control_max': max(ctrl),
    'gradient_maps': {'sv_sym': [float(x) for x in Ss], 'sv_anti': [float(x) for x in Sa],
                      'rank_sym': int(rank_s), 'rank_anti': int(rank_a),
                      'rotation_equivariance': float(max(abs(x) for x in (Jm * rot_m)))},
    'anti_8x11': {'orbit_rep_rows': [int(r) for r in anti_rows], 'used_rows': [int(r) for r in rows8],
                  'pivot_cols': [int(c) for c in cols8], 'minor_det': mp.nstr(det8, 16),
                  'sv': [float(x) for x in S8], 'kernel_dim': 3,
                  'kernel_residual': float(res_k), 'rotation_in_kernel_res': float(res_rot),
                  'rotation_fit_residual': float(fit)},
    'lambda': {'values': [float(x) for x in lam], 'residual_dps': float(resL),
               'reflection_symmetry': float(lam_sym)},
    'blocks': {'mixed_max': float(max(abs(x) for x in mixed)),
               'commutator_max': float(max(abs(x) for x in (SIGm * HW - HW * SIGm))),
               'hw_rot_max': float(max(abs(x) for x in hwr)),
               'sym_2x2_eig': [float(x) for x in ev2s],
               'anti_3x3_eig': [float(x) for x in ev3],
               'anti_quotient_2x2_eig': [float(x) for x in ev2],
               'anti_maxform_value': float(best_val)},
    'gauge': {'kappa_Fout_4y2': mp.nstr(kap, 20), 'Fout': mp.nstr(Fout, 16), 'y': mp.nstr(y_sig, 16),
              'full_space_gap': float(abs(d2_fex - kap * d2_pin)),
              'kernel_pairs': [list(map(str, t)) for t in rows]},
    'metric': {'pullback_gap': float(max(abs(x) for x in (chap - chap2))),
               'sym_eig_physical': [float(x) for x in ev2s],
               'sym_eig_chart_metric': [float(x) for x in ev_z],
               'metric_G_eig': [float(x) for x in np.linalg.eigvalsh(Gz)]},
    'repro': 'py -3 -B -X utf8 r20_physical_kkt_kernel.py',
})
(P / 'r20_physical_kkt_kernel.json').write_text(json.dumps(OUT, indent=2))
(P / 'r20_physical_kkt_kernel.log').write_text('\n'.join(REP) + '\n')
say('\nwritten r20_physical_kkt_kernel.json / .log')
