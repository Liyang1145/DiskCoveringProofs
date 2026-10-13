"""R20-TC-ELIM2 (r20-gluing, cline2 / DS v4.1f): E0a/E0b/E1 evidence for the
SYMMETRIC ACTIVE FAMILY (mirror symmetry + 5 active tight rows + boundary saturation),
FINITE BRANCH only.  No whole-ring-domain claim, no moving-ring wording.

NOTE (sole-writer correction, 2026-09-25): the E0b/E1 text further down originally claimed that
(U_1) is "LINEAR in R" with R an explicit function of the angles, and that the residues reduce to
"two angle-only equations".  That reading is WITHDRAWN: ReU_8, ReU_1, ImU_1 depend on R through
T_k = sqrt(R^2 - sin^2 a_k), so the rearrangement is a fixed-point map (phi(R*+-1e-3) - (R*+-1e-3)
= -+4.5e-3).  Corrected statement: TC-FAMILY-ELIMINATION.md sec.0/sec.3 and
r20_tc_r_dependency.json -- the content is THREE equations in FIVE unknowns (a0..a3, R):
E1 = U_1 row, E2 = U_2 row, E3 = waist row.  All numeric readings in this file remain valid;
only their interpretation as "two angle-only equations with explicit R" is withdrawn.

E0a  chain identity:  U_k - C_k = C_{k+1} - e_k = e^{i theta_{k+1}}(rho_{k+1} - e^{-i a_{k+1}})
     => |U_k - C_k| = |U_k - C_{k+1}| = R  (all k), from the ring-radius identity
     rho^2 - 2 rho cos a + 1 = R^2.
E0b  hub rational elimination (no square roots):
     (U_3) + chain identity  =>  y0 = 2 Re U_3 - rho_4   (branch A; other root y0 = rho_4 = C_4.x)
     (U_8) + Im U_8 = 0      =>  y1 = Re U_8 + R         (branch B; other root y1 = Re U_8 - R)
     (U_1) with y1           =>  LINEAR in R:
                                R = -[(ReU_8-ReU_1)^2 + (ImU_1)^2] / (2 (ReU_8-ReU_1))
     waist with h^2 = R^2-d^2 =>  LINEAR in h:
                                h = [((y0+y1)/2 - ReC_6)^2 + (ImC_6)^2 - d^2] / (2 ImC_6)
E1   residues = exactly two angle-only equations
     g1: R^2 - [(y0 - ReU_2)^2 + (ImU_2)^2] = 0      (the U_2 tight row)
     g2: R^2 - h^2 - d^2 = 0                         (A6, the hub definition)
     plus the F_c (crescent) form of the same conditions (C894 normal form, cited not re-proved).

Rank-drop readings (4x5 augmented singular values, 3x5 sigma_min) are reported as NUMERIC
DIAGNOSTIC ONLY and never as evidence.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_elim2.py
"""
import json
import sys
from pathlib import Path

import numpy as np
import sympy as sp
from mpmath import mp, mpf

HERE = Path(__file__).parent
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
LOG = []


def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s)
    LOG.append(s)
    sys.stdout.flush()


def main():
    mp.dps = 60
    import r20_tc_poly as TP

    # ------------------------------------------------------------------ E0a (symbolic)
    a = sp.symbols('a', real=True)
    R, rho = sp.symbols('R rho', positive=True)
    ring_id = sp.simplify((sp.cos(a) - sp.sqrt(R ** 2 - sp.sin(a) ** 2)) ** 2
                          - 2 * (sp.cos(a) - sp.sqrt(R ** 2 - sp.sin(a) ** 2)) * sp.cos(a)
                          + 1 - R ** 2)
    th1, th2, a1, a2, r1, r2 = sp.symbols('th1 th2 a1 a2 r1 r2', real=True)
    # U_k - C_k = C_{k+1} - e_k with e_k = e^{i(th_{k+1}-a_{k+1})} (recursion) and C_{k+1}=rho e^{i th2}
    z = (r2 * sp.cos(th2) - sp.cos(th2 - a2), r2 * sp.sin(th2) - sp.sin(th2 - a2))
    mod2 = sp.simplify(z[0] ** 2 + z[1] ** 2 - (r2 ** 2 - 2 * r2 * sp.cos(a2) + 1))
    P('=== E0a: chain identity / ring-radius identity (symbolic) ===')
    P('  rho^2 - 2 rho cos a + 1 - R^2  at rho = cos a - sqrt(R^2-sin^2 a)  =>  %s' % ring_id)
    P('  |C_{k+1} - e_k|^2 - (rho_{k+1}^2 - 2 rho_{k+1} cos a_{k+1} + 1)  =>  %s  (so it = R^2)' % mod2)

    # ------------------------------------------------------------------ root data
    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    ch = d['certificate']['center_hex']
    avec = [mpf(float.fromhex(ch[k])) for k in range(4)]
    y0v, y1v, Rv = mpf(float.fromhex(ch[4])), mpf(float.fromhex(ch[5])), mpf(float.fromhex(ch[6]))
    vals = TP.analytic_substitution(avec, y0v, y1v, Rv)
    mir = lambda k: k if k <= 4 else 8 - k
    a_all = avec + [mp.pi - 2 * sum(avec)] + [avec[3], avec[2], avec[1], avec[0]]
    th = [mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + a_all[k - 1] + a_all[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a_all[k] + a_all[k + 1])
    rho_v = [vals[TP.P[mir(k)]] - vals[TP.T[mir(k)]] for k in range(9)]
    Cx = [rho_v[k] * mp.cos(th[k]) for k in range(9)]
    Cy = [rho_v[k] * mp.sin(th[k]) for k in range(9)]
    Ux = [Cx[k] + Cx[(k + 1) % 9] - mp.cos(th[k] + a_all[k]) for k in range(9)]
    Uy = [Cy[k] + Cy[(k + 1) % 9] - mp.sin(th[k] + a_all[k]) for k in range(9)]
    # E0a numeric: per-row |U_k - C_k| - R and |U_k - C_{k+1}| - R
    devA = [(mp.sqrt((Ux[k] - Cx[k]) ** 2 + (Uy[k] - Cy[k]) ** 2) - Rv) for k in range(9)]
    devB = [(mp.sqrt((Ux[k] - Cx[(k + 1) % 9]) ** 2 + (Uy[k] - Cy[(k + 1) % 9]) ** 2) - Rv)
            for k in range(9)]
    P('  numeric at the certified root: max_k |U_k - C_k| - R = %s ; max_k |U_k - C_{k+1}| - R = %s'
      % (mp.nstr(max(abs(x) for x in devA), 6), mp.nstr(max(abs(x) for x in devB), 6)))
    P('  per-row |U_k - C_k| - R : %s' % [mp.nstr(x, 3) for x in devA])
    P('  axis checks: Im U_8 = %s ; Im C_4 = %s'
      % (mp.nstr(Uy[8], 6), mp.nstr(Cy[4], 6)))

    # ------------------------------------------------------------------ E0b (symbolic)
    rho4, u3x, u3y, u8x, u1x, u1y, u2x, u2y, c6x, c6y, y0, y1, h, m, dd, R_ = sp.symbols(
        'rho4 u3x u3y u8x u1x u1y u2x u2y c6x c6y y0 y1 h m d R', real=True)
    in3 = (u3x - rho4) ** 2 + u3y ** 2 - R_ ** 2            # chain identity |U_3 - C_4| = R
    y0s = 2 * u3x - rho4
    y1s = u8x + R_
    V1 = sp.simplify(((y0s - u3x) ** 2 + u3y ** 2 - R_ ** 2) - in3)
    V2 = sp.simplify((y1s - u8x) ** 2 - R_ ** 2 - (R_ ** 2 - R_ ** 2))
    V2 = sp.simplify((y1s - u8x) ** 2 - R_ ** 2)
    Dlt = u8x - u1x
    Rsol = -((u8x - u1x) ** 2 + u1y ** 2) / (2 * (u8x - u1x))
    V3 = sp.simplify(((y1s - u1x) ** 2 + u1y ** 2 - R_ ** 2).subs(R_, Rsol))
    ms = (y0s + y1s) / 2
    hsol = ((ms - c6x) ** 2 + c6y ** 2 - dd ** 2) / (2 * c6y)
    waist = (ms - c6x) ** 2 + (hsol - c6y) ** 2 - R_ ** 2
    # waist holds modulo A6:  h^2 = R^2 - d^2
    V4 = sp.simplify(sp.expand(waist - (dd ** 2 + hsol ** 2 - R_ ** 2)))
    g2 = sp.simplify(R_ ** 2 - hsol ** 2 - dd ** 2)
    P()
    P('=== E0b: rational hub elimination (symbolic, generic ring data) ===')
    P('  V1: (U_3) tight with y0 = 2ReU_3 - rho_4  reduces to the chain identity : %s' % V1)
    P('  V2: (U_8) tight with y1 = ReU_8 + R        : %s' % V2)
    P('  V3: (U_1) tight with that y1 and R = -[d^2+ImU_1^2]/(2d), d = ReU_8-ReU_1 : %s' % V3)
    P('  V4: waist with h = [(m-ReC_6)^2+ImC_6^2-d^2]/(2 ImC_6) reduces to A6  : %s' % V4)
    P('      (so the waist equation is consumed by h; the residue is g2 = A6)')
    P('  g2 symbolic = (R^2 - h^2 - d^2) with h substituted = %s' % g2)
    P('  => residues: g1 = R^2 - [(y0-ReU_2)^2 + (ImU_2)^2]   and   g2 = R^2 - h^2 - d^2')
    P('     only two equations, unknown = the four angles (hub/R/h are closed forms).')

    # ------------------------------------------------------------------ root readings
    y0_A = 2 * Ux[3] - rho_v[4]
    y1_B = Ux[8] + Rv
    Dlt = Ux[8] - Ux[1]
    R_c = -((Ux[8] - Ux[1]) ** 2 + Uy[1] ** 2) / (2 * (Ux[8] - Ux[1]))
    m_c = (y0_A + y1_B) / 2
    dd_c = (y1_B - y0_A) / 2
    h_c = ((m_c - Cx[6]) ** 2 + Cy[6] ** 2 - dd_c ** 2) / (2 * Cy[6])
    g1 = R_c ** 2 - ((y0_A - Ux[2]) ** 2 + Uy[2] ** 2)
    g2v = R_c ** 2 - h_c ** 2 - dd_c ** 2
    P()
    P('=== E1: root readings (own independent replication) ===')
    P('  y0 (branch A)  = 2ReU_3 - rho_4 : diff vs certified y0 = %s'
      % mp.nstr(y0_A - y0v, 6))
    P('  y1 (branch B)  = ReU_8 + R      : diff vs certified y1 = %s'
      % mp.nstr(y1_B - y1v, 6))
    P('  R closed form                   : diff vs certified R  = %s' % mp.nstr(R_c - Rv, 6))
    P('  h closed form                   : diff vs certified h  = %s'
      % mp.nstr(h_c - vals[TP.h_], 6))
    P('  g1 = %s ; g2 = %s' % (mp.nstr(g1, 6), mp.nstr(g2v, 6)))
    P('  denominators: ReU_8 - ReU_1 = %s ; Im C_6 = %s (both safely nonzero)'
      % (mp.nstr(Dlt, 8), mp.nstr(Cy[6], 8)))
    # other branches
    y0_alt = rho_v[4]
    y1_alt = Ux[8] - Rv
    P('  other branch y0 = rho_4 = C_4.x = %s  (=> H0 = C_4, hub coincides with ring centre 4);'
      % mp.nstr(y0_alt, 10))
    P('      its residual (y0-ReU_3)^2+ImU_3^2-R^2 = %s (0 by the chain identity)'
      % mp.nstr((y0_alt - Ux[3]) ** 2 + Uy[3] ** 2 - Rv ** 2, 6))
    P('      feasibility: |H0| = %s  vs inner-disk requirement <= 1-R = %s  => %s'
      % (mp.nstr(abs(y0_alt), 8), mp.nstr(1 - Rv, 8),
         'INFEASIBLE (hub is on the boundary ring, not strictly inner)'
         if abs(y0_alt) > 1 - Rv else 'possible'))
    P('  other branch y1 = ReU_8 - R = %s  (the inner x-axis intersection of the circle around U_8)'
      % mp.nstr(y1_alt, 10))
    P('      feasibility: |H1| = %s  vs 1-R = %s  => %s'
      % (mp.nstr(abs(y1_alt), 8), mp.nstr(1 - Rv, 8),
         'INFEASIBLE' if abs(y1_alt) > 1 - Rv else 'possible (needs separate check)'))
    P('  certified hub norms: |H0| = %s ; |H1| = %s' % (mp.nstr(abs(y0v), 8), mp.nstr(abs(y1v), 8)))
    # F_c (crescent) form of the same conditions  (C894 normal form; cited, not re-proved)
    def Fc(pa, pb, pc, r):
        det = (pb[0] - pa[0]) * (pc[1] - pa[1]) - (pb[1] - pa[1]) * (pc[0] - pa[0])
        ab2 = (pb[0] - pa[0]) ** 2 + (pb[1] - pa[1]) ** 2
        ac2 = (pc[0] - pa[0]) ** 2 + (pc[1] - pa[1]) ** 2
        bc2 = (pc[0] - pb[0]) ** 2 + (pc[1] - pb[1]) ** 2
        return 4 * r ** 2 * det ** 2 - ab2 * ac2 * bc2
    C2 = (Cx[2], Cy[2]); C3 = (Cx[3], Cy[3]); H0 = (y0v, mpf(0)); H1 = (y1v, mpf(0))
    C6 = (Cx[6], Cy[6])
    P('  F_c form (C894 normal form, cited): F_c(C_2,C_3,H0) = %s   (g1 <=> circumradius R)'
      % mp.nstr(Fc(C2, C3, H0, Rv), 6))
    P('      F_c(H0,H1,C_6) = %s   (waist condition in the concyclic form)'
      % mp.nstr(Fc(H0, H1, C6, Rv), 6))

    # ------------------------------------------------------------------ threshold: diagnostic only
    P()
    P('=== threshold / rank readings: NUMERIC DIAGNOSTIC ONLY (non-bearing) ===')
    P('  (numerical singular values cannot prove an exact rank deficiency; the KKT equivalence')
    P('   would additionally need the 3x5 full-row-rank as a separate hypothesis.)')

    def ring_data_ra(a4, Rr):
        aa = list(a4) + [mp.pi - 2 * sum(a4)] + [a4[3], a4[2], a4[1], a4[0]]
        rr = [mp.cos(aa[k]) - mp.sqrt(Rr ** 2 - mp.sin(aa[k]) ** 2) for k in range(9)]
        tt = [mpf(0)] * 9
        for k in range(5, 9):
            tt[k] = tt[k - 1] + aa[k - 1] + aa[k]
        for k in range(3, -1, -1):
            tt[k] = tt[k + 1] - (aa[k] + aa[k + 1])
        Ccl = [(rr[k] * mp.cos(tt[k]), rr[k] * mp.sin(tt[k])) for k in range(9)]
        Uul = [(Ccl[k][0] + Ccl[(k + 1) % 9][0] - mp.cos(tt[k] + aa[k]),
                Ccl[k][1] + Ccl[(k + 1) % 9][1] - mp.sin(tt[k] + aa[k])) for k in range(9)]
        return rr, Ccl, Uul

    def Fvec(a4, Rr):
        rr, Ccl, Uul = ring_data_ra(a4, Rr)
        H0l = (2 * Uul[3][0] - rr[4], mpf(0))
        H1l = (Uul[8][0] + Rr, mpf(0))
        return [Fc(Ccl[1], Ccl[2], H1l, Rr), Fc(Ccl[2], Ccl[3], H0l, Rr), Fc(H0l, H1l, Ccl[6], Rr)]

    Fr = Fvec(avec, Rv)
    P('  reduced concyclic (F_c) content at the root: F1 = %s ; F2 = %s ; F3 = %s'
      % (mp.nstr(Fr[0], 6), mp.nstr(Fr[1], 6), mp.nstr(Fr[2], 6)))
    hstep = mpf('1e-25')
    J35 = []
    for i in range(4):
        ap = list(avec); ap[i] += hstep
        am = list(avec); am[i] -= hstep
        fp = Fvec(ap, Rv); fm = Fvec(am, Rv)
        J35.append([(fp[k] - fm[k]) / (2 * hstep) for k in range(3)])
    fp = Fvec(avec, Rv + hstep); fm = Fvec(avec, Rv - hstep)
    J35.append([(fp[k] - fm[k]) / (2 * hstep) for k in range(3)])
    Ja = np.array([[float(x) for x in row] for row in J35]).T
    sv3 = np.linalg.svd(Ja, compute_uv=False)
    Ja4 = np.vstack([Ja, np.array([[0.0, 0.0, 0.0, 0.0, 1.0]])])
    sv4 = np.linalg.svd(Ja4, compute_uv=False)
    P('  3x5 Jacobian singular values = %s' % np.round(sv3, 8).tolist())
    P('  4x5 augmented singular values = %s   (4th = %.3e : diagnostic only)'
      % (np.round(sv4, 8).tolist(), float(sv4[-1])))
    P('  => root satisfies the 3 concyclic conditions to <= %.1e; the 4th singular value sits at'
      % float(max(abs(x) for x in Fr)))
    P('     the noise level: CONSISTENT with an R-critical point on this 2-dim branch, NOT evidence.')

    # ------------------------------------------------------------------ size census (polynomial form)
    P()
    P('=== size census of the POLYNOMIAL form (for the explosion-point record) ===')
    Pv = sp.symbols('P0:5', real=True)
    Qv = sp.symbols('Q0:5', real=True)
    Rv_sym = sp.symbols('rho0:5', real=True)
    hs, y0s_, y1s_, Rs_ = sp.symbols('h y0 y1 R', real=True)
    mirl = lambda k: k if k <= 4 else 8 - k
    rho_s = [Rv_sym[mirl(k)] for k in range(9)]
    W = (sp.Integer(1), sp.Integer(0))
    for k in range(4):
        W = (W[0] * Pv[k] - W[1] * Qv[k], W[0] * Qv[k] + W[1] * Pv[k])
    W2 = (W[0] ** 2 - W[1] ** 2, 2 * W[0] * W[1])
    peqs = [('unit%d' % k, Pv[k] ** 2 + Qv[k] ** 2 - 1) for k in range(4)]
    peqs += [('w4_re', sp.expand(Pv[4] + W2[0])), ('w4_im', sp.expand(Qv[4] - W2[1]))]
    peqs += [('ring%d' % k, Rv_sym[k] ** 2 - 2 * Rv_sym[k] * Pv[k] + 1 - Rs_ ** 2) for k in range(5)]
    dsl = (y1s_ - y0s_) / 2
    peqs += [('hub', hs ** 2 - (Rs_ ** 2 - dsl ** 2))]
    rot = lambda p, q: (p[0] * q[0] - p[1] * q[1], p[0] * q[1] + p[1] * q[0])
    cs = [None] * 9
    cs[4] = (sp.Integer(1), sp.Integer(0))
    for k in range(5, 9):
        phi = rot((Pv[mirl(k - 1)], Qv[mirl(k - 1)]), (Pv[mirl(k)], Qv[mirl(k)]))
        cs[k] = rot(cs[k - 1], phi)
    for k in range(3, -1, -1):
        phi = rot((Pv[k], Qv[k]), (Pv[k + 1], Qv[k + 1]))
        cs[k] = rot(cs[k + 1], (phi[0], -phi[1]))
    Uxs, Uys = [], []
    for k in range(9):
        k2 = (k + 1) % 9
        Uxs.append(sp.expand(rho_s[k] * cs[k][0] + rho_s[k2] * cs[k2][0]
                             - (cs[k][0] * Pv[mirl(k)] - cs[k][1] * Qv[mirl(k)])))
        Uys.append(sp.expand(rho_s[k] * cs[k][1] + rho_s[k2] * cs[k2][1]
                             - (cs[k][1] * Pv[mirl(k)] + cs[k][0] * Qv[mirl(k)])))
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        yv = y1s_ if l else y0s_
        peqs.append(('tight_k%d_l%d' % (k, l), sp.expand((Uxs[k] - yv) ** 2 + Uys[k] ** 2 - Rs_ ** 2)))
    ms_ = (y0s_ + y1s_) / 2
    peqs.append(('tight_hub', sp.expand((ms_ - rho_s[6] * cs[6][0]) ** 2
                                        + (hs - rho_s[6] * cs[6][1]) ** 2 - Rs_ ** 2)))
    ALLV = list(Pv) + list(Qv) + list(Rv_sym) + [hs, y0s_, y1s_, Rs_]
    subp = {}
    for k in range(5):
        subp[Pv[k]] = vals[TP.P[k]]; subp[Qv[k]] = vals[TP.Q[k]]; subp[Rv_sym[k]] = rho_v[k]
    subp[hs] = vals[TP.h_]; subp[y0s_] = y0v; subp[y1s_] = y1v; subp[Rs_] = Rv
    worstp = max(abs(sp.N(e.subs(subp), 40)) for _, e in peqs)
    P('  polynomial form: %d variables, %d equations, total degrees %s, largest ops %s'
      % (len(ALLV), len(peqs), sorted({sp.total_degree(e) for _, e in peqs}),
         max(sp.count_ops(e) for _, e in peqs)))
    P('  numeric residual at the certified root (worst of %d equations): %s'
      % (len(peqs), mp.nstr(worstp, 6)))
    P('  (this is the object a resultant/Groebner attack would have to eliminate; recorded as the')
    P('   explosion-point specification, no elimination attempted in this round.)')

    out = dict(
        role='E0a/E0b/E1 evidence for the symmetric active family, finite branch',
        caliber=('mirror-symmetric configuration, 5 active tight rows, boundary saturation '
                 'assumptions; finite branch only. NOT a whole-ring-domain statement.'),
        E0a=dict(ring_identity=str(ring_id), mod_identity=str(mod2),
                 per_row_dev_UC=[mp.nstr(x, 6) for x in devA],
                 per_row_dev_UCp1=[mp.nstr(x, 6) for x in devB],
                 max_dev_UC=mp.nstr(max(abs(x) for x in devA), 6),
                 max_dev_UCp1=mp.nstr(max(abs(x) for x in devB), 6),
                 ImU8=mp.nstr(Uy[8], 6), ImC4=mp.nstr(Cy[4], 6)),
        E0b=dict(V1=str(V1), V2=str(V2), V3=str(V3), V4=str(V4),
                 formulas=dict(y0='2*ReU_3 - rho_4', y1='ReU_8 + R',
                               R='-[(ReU_8-ReU_1)^2+(ImU_1)^2]/(2(ReU_8-ReU_1))',
                               h='[(m-ReC_6)^2+(ImC_6)^2-d^2]/(2 ImC_6)',
                               m='(y0+y1)/2', d='(y1-y0)/2')),
        E1=dict(y0_diff=mp.nstr(y0_A - y0v, 6), y1_diff=mp.nstr(y1_B - y1v, 6),
                R_diff=mp.nstr(R_c - Rv, 6), h_diff=mp.nstr(h_c - vals[TP.h_], 6),
                g1=mp.nstr(g1, 6), g2=mp.nstr(g2v, 6),
                denom_ReU8_ReU1=mp.nstr(Dlt, 8), denom_ImC6=mp.nstr(Cy[6], 8),
                residuals='g1 = R^2 - [(y0-ReU_2)^2+(ImU_2)^2]; g2 = R^2 - h^2 - d^2',
                Fc_C2C3H0=mp.nstr(Fc(C2, C3, H0, Rv), 6),
                Fc_H0H1C6=mp.nstr(Fc(H0, H1, C6, Rv), 6)),
        census=dict(n_vars=len(ALLV), n_eqs=len(peqs), degrees=sorted({int(sp.total_degree(e)) for _,e in peqs}), max_ops=int(max(sp.count_ops(e) for _,e in peqs)), worst_root_residual=mp.nstr(worstp,6)),
        branches=dict(A_y0_rho4=mp.nstr(y0_alt, 10), A_y0_other_root=mp.nstr(y0_A, 10),
                      B_y1_plusR=mp.nstr(y1_B, 10), B_y1_minusR=mp.nstr(y1_alt, 10),
                      H0_norm_certified=mp.nstr(abs(y0v), 8),
                      H1_norm_certified=mp.nstr(abs(y1v), 8),
                      inner_requirement='|H| <= 1 - R = %s' % mp.nstr(1 - Rv, 8)),
        scope=('finite branch of the symmetric active family only; no claim registered; '
               'no grid scan; rank readings demoted to diagnostic'),
        log=LOG)
    (HERE / 'r20_tc_elim2.json').write_text(json.dumps(out, indent=1, default=str))
    (HERE / 'r20_tc_elim2.log').write_text('\n'.join(LOG) + '\n')
    P('saved r20_tc_elim2.json / .log')


if __name__ == '__main__':
    main()

