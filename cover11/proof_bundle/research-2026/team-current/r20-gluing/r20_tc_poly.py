"""R20-TC-POLY (r20-gluing, cline2/DS v4.1f): the 5 TC residuals rewritten as a POLYNOMIAL system
(squared distances + unit-complex cos/sin), with the branch equivalence made explicit.

NO Groebner / no elimination (as instructed).  Produced here:
  * 37 real variables, 35 polynomial equations with integer coefficients -- no pi, no sin/cos/sqrt
    survives in the equations themselves;
  * the structural split: 30 of the 35 equations are DEFINITIONAL IDENTITIES (they hold for every
    legal tuple), the remaining 5 are the genuine residual conditions;
  * the branch data: 5 sign choices t_k = +-sqrt(R^2 - sin^2 a_k) and 1 sign choice h = +-sqrt(...),
    i.e. 64 algebraic branches, of which exactly (+,...,+,+) is the analytic one; the 4
    squared-distance substitutions carry NO branch ambiguity because R > 0 is declared;
  * checks: symbolic pairwise complex-multiplication identity, identity-class checks at random
    parameter points, vanishing of all 35 equations at the certified root image (mp.dps = 60),
    branch margins, ranks (analytic 5 <-> dim 2 ; algebraic 35 <-> dim 2), and discriminating
    controls (perturbation / wrong branch).

Analytic model (r20_tc_iv1.symbolic_res5 == tc_s32_kraw.res5, C366):
  x = (a0,a1,a2,a3,y0,y1,R);  a = (a0,a1,a2,a3,a4,a3,a2,a1,a0),  a4 = pi - 2(a0+a1+a2+a3)
  rho_k = cos a_k - sqrt(R^2 - sin^2 a_k),   th_4 = 0,  th_k = th_{k-1}+a_{k-1}+a_k (k>=5),
  th_k = th_{k+1}-(a_k+a_{k+1}) (k<=3),      C_k = rho_k (cos th_k, sin th_k),
  U_k = C_k + C_{k+1} - (cos(th_k+a_k), sin(th_k+a_k))       (indices mod 9)
  f = |U_k - (y_l,0)| - R for (k,l) in {(1,1),(2,0),(3,0),(8,1)},  f5 = |C_6 - (m,h)| - R,
  m = (y0+y1)/2, d = (y1-y0)/2, h = sqrt(R^2 - d^2).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_poly.py
"""
import json
import sys
from pathlib import Path

import sympy as sp
from mpmath import mp, mpf

HERE = Path(__file__).parent
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(HERE))

P = sp.symbols('P0:5', real=True)          # P_k = cos a_k
Q = sp.symbols('Q0:5', real=True)          # Q_k = sin a_k
CC = sp.symbols('c0:9', real=True)         # c_k = cos th_k
SS = sp.symbols('s0:9', real=True)         # s_k = sin th_k
T = sp.symbols('t0:5', real=True)          # t_k = sqrt(R^2 - sin^2 a_k)  (> 0 on the branch)
h_, y0_, y1_, R_ = sp.symbols('h y0 y1 R', real=True)
VARS = list(P) + list(Q) + list(CC) + list(SS) + list(T) + [h_, y0_, y1_, R_]
IDENT = 'identity'      # holds for every legal tuple (definitions / bookkeeping)
COND = 'condition'      # the genuine residual condition


def mir(k):
    return k if k <= 4 else 8 - k


def cmul(w1, w2):
    (a1, b1), (a2, b2) = w1, w2
    return (a1 * a2 - b1 * b2, a1 * b2 + b1 * a2)


def build():
    eqs = []            # (name, kind, expression)

    def add(nm, kind, e):
        eqs.append((nm, kind, sp.expand(e)))

    for k in range(4):
        add('unit_w%d' % k, IDENT, P[k] ** 2 + Q[k] ** 2 - 1)
    W = (sp.Integer(1), sp.Integer(0))
    for k in range(4):
        W = cmul(W, (P[k], Q[k]))
    W2 = cmul(W, W)                                        # == e^{2 i sigma}
    add('w4_real', IDENT, P[4] + W2[0])                    # cos(pi-2s) = -cos 2s
    add('w4_imag', IDENT, Q[4] - W2[1])                    # sin(pi-2s) = +sin 2s
    for k in range(5, 9):
        phi = cmul((P[mir(k - 1)], Q[mir(k - 1)]), (P[mir(k)], Q[mir(k)]))
        add('rotp_c%d' % k, IDENT, CC[k] - (CC[k - 1] * phi[0] - SS[k - 1] * phi[1]))
        add('rotp_s%d' % k, IDENT, SS[k] - (CC[k - 1] * phi[1] + SS[k - 1] * phi[0]))
    for k in range(4):
        phi = cmul((P[k], Q[k]), (P[k + 1], Q[k + 1]))
        add('rotm_c%d' % k, IDENT, CC[k] - (CC[k + 1] * phi[0] + SS[k + 1] * phi[1]))
        add('rotm_s%d' % k, IDENT, SS[k] - (-CC[k + 1] * phi[1] + SS[k + 1] * phi[0]))
    add('norm_c4', IDENT, CC[4] - 1)
    add('norm_s4', IDENT, SS[4])
    for k in range(5):
        add('t%d' % k, IDENT, T[k] ** 2 - (R_ ** 2 - Q[k] ** 2))
    d_ = (y1_ - y0_) / 2
    add('hub_h', IDENT, h_ ** 2 - (R_ ** 2 - d_ ** 2))
    rho = [P[mir(k)] - T[mir(k)] for k in range(9)]
    Ux, Uy = [], []
    for k in range(9):
        k2 = (k + 1) % 9
        Ux.append(rho[k] * CC[k] + rho[k2] * CC[k2] - (CC[k] * P[mir(k)] - SS[k] * Q[mir(k)]))
        Uy.append(rho[k] * SS[k] + rho[k2] * SS[k2] - (SS[k] * P[mir(k)] + CC[k] * Q[mir(k)]))
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        yv = y1_ if l else y0_
        add('res_k%d_l%d' % (k, l), COND, (Ux[k] - yv) ** 2 + Uy[k] ** 2 - R_ ** 2)
    m_ = (y0_ + y1_) / 2
    add('res_hub', COND, (m_ - rho[6] * CC[6]) ** 2 + (h_ - rho[6] * SS[6]) ** 2 - R_ ** 2)
    return eqs, Ux, Uy, rho


def eval_num(e, vals):
    """numeric evaluation of a polynomial expression with mpf leaves"""
    if e.is_Symbol:
        return vals[e]
    if e.is_Integer:
        return mpf(int(e))
    if e.is_Rational:
        return mpf(int(e.p)) / mpf(int(e.q))
    if e.is_Add:
        return sum((eval_num(a, vals) for a in e.args), mpf(0))
    if e.is_Mul:
        r = mpf(1)
        for a in e.args:
            r *= eval_num(a, vals)
        return r
    if e.is_Pow:
        b, ex = e.args
        return eval_num(b, vals) ** int(ex)
    raise NotImplementedError(str(e.func))


def analytic_substitution(av, y0v, y1v, Rv):
    """the map Phi: analytic tuple -> algebraic point (cos/sin/t/h image)"""
    a = list(av) + [mp.pi - 2 * sum(av)] + [av[3], av[2], av[1], av[0]]
    th = [None] * 9
    th[4] = mpf(0)
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    vals = {}
    for k in range(5):
        vals[P[k]] = mp.cos(a[k])
        vals[Q[k]] = mp.sin(a[k])
        vals[T[k]] = mp.sqrt(Rv ** 2 - mp.sin(a[k]) ** 2)          # + branch
    for k in range(9):
        vals[CC[k]] = mp.cos(th[k])
        vals[SS[k]] = mp.sin(th[k])
    vals[h_] = mp.sqrt(Rv ** 2 - ((y1v - y0v) / 2) ** 2)
    vals[y0_], vals[y1_], vals[R_] = y0v, y1v, Rv
    return vals


def main():
    iv3 = __import__('r20_tc_iv3')
    print('=== R20-TC-POLY: the 5 TC residuals as a polynomial root definition ===')
    eqs, Ux, Uy, rho = build()
    names = [e[0] for e in eqs]
    kinds = [e[1] for e in eqs]
    print('variables: %d ; equations: %d (identity %d, condition %d)'
          % (len(VARS), len(eqs), kinds.count(IDENT), kinds.count(COND)))
    degs = [sp.Poly(e[2], *VARS).total_degree() for e in eqs]
    print('total degrees: %s' % sorted(set(degs)))
    print('coefficients outside Z: %s' % (sorted({str(c) for e in eqs
                                                  for c in sp.Poly(e[2], *VARS).coeffs()
                                                  if not c.is_Integer}) or 'NONE'))
    print('pi / Float / sin / cos / sqrt nodes in the 35 equations: %d / %d / %d / %d / %d'
          % (sum(1 for e in eqs if e[2].has(sp.pi)), sum(1 for e in eqs if e[2].has(sp.Float)),
             sum(1 for e in eqs if e[2].has(sp.sin)), sum(1 for e in eqs if e[2].has(sp.cos)),
             sum(1 for e in eqs if e[2].has(sp.sqrt))))

    # ---------------- symbolic lemmas
    print()
    print('--- symbolic lemmas behind the reformulation ---')
    x, yv = sp.symbols('x yv', real=True)
    L1 = sp.simplify(sp.expand_complex((sp.cos(x) + sp.I * sp.sin(x))
                                       * (sp.cos(yv) + sp.I * sp.sin(yv))
                                       - (sp.cos(x + yv) + sp.I * sp.sin(x + yv))))
    L2 = (sp.simplify(sp.cos(sp.pi - 2 * x) + sp.cos(2 * x)),
          sp.simplify(sp.sin(sp.pi - 2 * x) - sp.sin(2 * x)))
    L3 = sp.simplify(sp.cos(x) ** 2 + sp.sin(x) ** 2 - 1)
    L4 = sp.simplify(sp.sqrt(x ** 2) ** 2 - x ** 2)
    print('  L1  product/angle-addition identity (C-multiplication)      : %s' % L1)
    print('  L2  pi-folding cos(pi-2x)=-cos2x , sin(pi-2x)=+sin2x        : %s' % (L2,))
    print('  L3  unit relation cos^2+sin^2=1                            : %s' % L3)
    print('  L4  (sqrt(q))^2 = q                                        : %s' % L4)
    print('  => L1 iterated 3x gives prod_{k<=3} w_k = e^{i sigma}, hence W^2 = e^{2 i sigma}')

    # ---------------- identity class vs condition class at RANDOM points
    print()
    print('--- identity class holds at random legal tuples; condition class does not ---')
    mp.dps = 50
    rng = [(mpf('0.37') + mpf('0.03') * i) for i in range(4)]
    for trial, av in enumerate([[mpf('0.30'), mpf('0.41'), mpf('0.25'), mpf('0.33')],
                                [mpf('0.42'), mpf('0.28'), mpf('0.35'), mpf('0.31')],
                                [mpf('0.20'), mpf('0.45'), mpf('0.38'), mpf('0.30')]]):
        Rv, y0v, y1v = mpf('0.55'), mpf('0.25'), mpf('-0.12')   # |sin a_k| < R : legal domain
        vals = analytic_substitution(av, y0v, y1v, Rv)
        wi = max(abs(eval_num(e[2], vals)) for e in eqs if e[1] == IDENT)
        wc = [eval_num(e[2], vals) for e in eqs if e[1] == COND]
        print('  trial %d: max|identity eq| = %-10s  ; condition eqs = %s'
              % (trial, mp.nstr(wi, 3), [mp.nstr(v, 4) for v in wc]))
    print('  (identities vanish to rounding at arbitrary tuples; the 5 conditions are the content)')

    # ---------------- own root refinement (own model, mp.dps = 60)
    print()
    print('--- certified root: own refinement (own SymPy model, mp.dps = 60) ---')
    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    cert = d['certificate']
    u = [mpf(v) for v in d['numeric_root']]
    trees, vs = iv3.build_model()
    mp.dps = 60
    Bp = iv3.MpfEngine()
    for it in range(6):
        F, J = iv3.system_jac_F(trees, vs, u, Bp, Bp)
        err = max(abs(v) for v in F)
        print('  newton %d: max|F| = %s' % (it, mp.nstr(err, 6)))
        if err < mpf('1e-55'):
            break
        du = mp.lu_solve(mp.matrix(J), mp.matrix([-v for v in F]))
        u = [u[i] + du[i] for i in range(12)]
    xstar = u[:7]
    print('  root (7 coords): %s' % [mp.nstr(v, 22) for v in xstar])
    inside = all(abs(u[i] - mpf(float.fromhex(cert['center_hex'][i])))
                 <= mpf(float.fromhex(cert['radius_hex'])) for i in range(12))
    print('  root inside the certified 12D box (r20_tc_iv3): %s' % inside)

    vals = analytic_substitution(xstar[:4], xstar[4], xstar[5], xstar[6])
    tab = [(e[0], e[1], eval_num(e[2], vals)) for e in eqs]
    worst = max(tab, key=lambda t: abs(t[2]))
    print()
    print('--- the 35 equations at the root image (mp.dps = 60) ---')
    for nm, kd, v in tab:
        print('     %-12s %-9s %s' % (nm, kd, mp.nstr(v, 5)))
    print('  max |equation| = %s at %s  ->  %s'
          % (mp.nstr(abs(worst[2]), 4), worst[0],
             'ALL 35 VANISH' if abs(worst[2]) < mpf('1e-50') else 'FAILURE'))

    # ---------------- branch data
    print()
    print('--- branch data at the image point (which signs the equivalence needs) ---')
    br = {}
    for k in range(5):
        br['t%d' % k] = vals[T[k]]
    br['h'] = vals[h_]
    br['R'] = xstar[6]
    for k in range(4):
        br['sin a%d' % k] = vals[Q[k]]
        br['cos a%d' % k] = vals[P[k]]
    br['rho_min'] = min(vals[P[mir(k)]] - vals[T[mir(k)]] for k in range(9))
    for k, v in br.items():
        print('     %-9s = %s' % (k, mp.nstr(v, 12)))
    ok_br = all(v > 0 for v in br.values())
    print('  all branch inequalities hold (>0): %s' % ok_br)

    # ---------------- backward leg: reconstruct the analytic tuple, rebuild the residuals
    print()
    print('--- backward leg: rebuild the analytic data from the algebraic point ---')
    a_rec = [mp.atan2(vals[Q[k]], vals[P[k]]) for k in range(4)]
    a_full = a_rec + [mp.pi - 2 * sum(a_rec)] + [a_rec[3], a_rec[2], a_rec[1], a_rec[0]]
    th_rec = [None] * 9
    th_rec[4] = mpf(0)
    for k in range(5, 9):
        th_rec[k] = th_rec[k - 1] + a_full[k - 1] + a_full[k]
    for k in range(3, -1, -1):
        th_rec[k] = th_rec[k + 1] - (a_full[k] + a_full[k + 1])
    dev_th = max(abs(mp.atan2(mp.sin(mp.atan2(vals[SS[k]], vals[CC[k]]) - th_rec[k]),
                              mp.cos(mp.atan2(vals[SS[k]], vals[CC[k]]) - th_rec[k])))
                 for k in range(9))
    dev_t = max(abs(mp.sqrt(vals[R_] ** 2 - vals[Q[k]] ** 2) - vals[T[k]]) for k in range(5))
    rho_rec = [vals[P[mir(k)]] - vals[T[mir(k)]] for k in range(9)]
    C_rec = [(rho_rec[k] * vals[CC[k]], rho_rec[k] * vals[SS[k]]) for k in range(9)]
    U_rec = []
    for k in range(9):
        k2 = (k + 1) % 9
        U_rec.append((C_rec[k][0] + C_rec[k2][0]
                      - (vals[CC[k]] * vals[P[mir(k)]] - vals[SS[k]] * vals[Q[mir(k)]]),
                      C_rec[k][1] + C_rec[k2][1]
                      - (vals[SS[k]] * vals[P[mir(k)]] + vals[CC[k]] * vals[Q[mir(k)]])))
    y0r, y1r, Rr = vals[y0_], vals[y1_], vals[R_]
    m_r, d_r = (y0r + y1r) / 2, (y1r - y0r) / 2
    h_r = mp.sqrt(Rr ** 2 - d_r ** 2)
    f_rec = []
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        yv = y1r if l else y0r
        f_rec.append(mp.sqrt((U_rec[k][0] - yv) ** 2 + U_rec[k][1] ** 2) - Rr)
    f_rec.append(mp.sqrt((m_r - C_rec[6][0]) ** 2 + (h_r - C_rec[6][1]) ** 2) - Rr)
    print('  max |theta_k(from (c,s)) - theta_k(recursion)| mod 2pi = %s' % mp.nstr(dev_th, 4))
    print('  max |t_k(R,sin a_k) - t_k variable|                        = %s' % mp.nstr(dev_t, 4))
    print('  reconstructed 5 residuals  |U-(y,0)|-R / |C6-(m,h)|-R      = %s'
          % [mp.nstr(v, 4) for v in f_rec])
    print('  h rebuilt from (R,d) minus h variable                      = %s'
          % mp.nstr(h_r - vals[h_], 4))
    back = dict(dev_theta=mp.nstr(dev_th, 4), dev_t=mp.nstr(dev_t, 4),
                residuals=[mp.nstr(v, 4) for v in f_rec], dev_h=mp.nstr(h_r - vals[h_], 4))

    # ---------------- controls
    print()
    print('--- controls ---')
    ctrl = {}
    xp = list(xstar)
    xp[0] += mpf('1e-6')
    valsp = analytic_substitution(xp[:4], xp[4], xp[5], xp[6])
    wp = max(abs(eval_num(e[2], valsp)) for e in eqs if e[1] == COND)
    ctrl['a0+1e-6'] = mp.nstr(wp, 4)
    print('  a0 shifted by 1e-6  : max |condition| = %s (was <= 1e-57)' % mp.nstr(wp, 4))
    vals2 = dict(vals)
    vals2[T[0]] = -vals[T[0]]                       # wrong branch: t0 -> -t0
    wb = abs(eval_num(eqs[names.index('res_k8_l1')][2], vals2))
    print('  wrong branch t0 -> -t0 : |res_k8_l1| = %s (rho_8 = P_0 - t_0 is affected)'
          % mp.nstr(wb, 4))
    ctrl['wrong_branch_t0'] = mp.nstr(wb, 4)
    # branch f5 (hub) sign
    vals3 = dict(vals)
    vals3[h_] = -vals[h_]
    print('  wrong branch h  -> -h  : |res_hub| = %s'
          % mp.nstr(abs(eval_num(eqs[names.index('res_hub')][2], vals3)), 4))
    ctrl['wrong_branch_h'] = mp.nstr(abs(eval_num(eqs[names.index('res_hub')][2], vals3)), 4)

    # ---------------- ranks / local dimension
    print()
    print('--- local dimension at the image point ---')
    xenv = {vs[k]: xstar[k] for k in range(7)}
    Jan = mp.matrix(5, 7)
    for m in range(5):
        for i in range(7):
            Jan[m, i] = iv3.ev(trees[1][m][i], xenv, Bp)
    _, S1, _ = mp.svd_r(Jan)
    sv1 = [S1[i] for i in range(5)]
    r1 = sum(1 for v in sv1 if v > mpf('1e-45'))
    print('  analytic 5x7 Jacobian singular values: %s ; rank %d => 7-5 = 2'
          % ([mp.nstr(v, 6) for v in sv1], r1))
    Jp = sp.Matrix([[sp.diff(e[2], vv) for vv in VARS] for e in eqs])
    Jn = mp.matrix(len(eqs), len(VARS))
    for i in range(len(eqs)):
        for j in range(len(VARS)):
            Jn[i, j] = eval_num(Jp[i, j], vals)
    _, S2, _ = mp.svd_r(Jn)
    sv2 = sorted((S2[i] for i in range(min(Jn.rows, Jn.cols))), reverse=True)
    r2 = sum(1 for v in sv2 if v > mpf('1e-45'))
    print('  algebraic 35x37 Jacobian: sigma_max = %s ; sigma_min = %s ; rank %d => 37-35 = 2'
          % (mp.nstr(sv2[0], 6), mp.nstr(sv2[-1], 6), r2))

    out = dict(role='polynomial reformulation of the 5 TC residuals + branch equivalence data',
               n_vars=len(VARS), n_eqs=len(eqs), n_identity=kinds.count(IDENT),
               n_condition=kinds.count(COND), names=names, kinds=kinds,
               total_degrees=sorted(set(degs)),
               noninteger_coefficients=sorted({str(c) for e in eqs
                                               for c in sp.Poly(e[2], *VARS).coeffs()
                                               if not c.is_Integer}),
               pi_nodes=sum(1 for e in eqs if e[2].has(sp.pi)),
               transcendental_nodes=sum(1 for e in eqs if e[2].has(sp.sin) or e[2].has(sp.cos)
                                        or e[2].has(sp.sqrt)),
               lemmas=dict(L1=str(L1), L2=[str(v) for v in L2], L3=str(L3), L4=str(L4)),
               root=[mp.nstr(v, 30) for v in xstar], root_inside_certified_box=bool(inside),
               max_equation_residual=mp.nstr(abs(worst[2]), 5), worst_equation=worst[0],
               equations=[[nm, kd, mp.nstr(v, 5)] for nm, kd, v in tab],
               branch={k: mp.nstr(v, 12) for k, v in br.items()},
               branch_all_positive=bool(ok_br), backward_leg=back,
               controls=ctrl,
               analytic_rank=r1, analytic_singular_values=[mp.nstr(v, 8) for v in sv1],
               algebraic_rank=r2, algebraic_sigma_max=mp.nstr(sv2[0], 8),
               algebraic_sigma_min=mp.nstr(sv2[-1], 8),
               scope='algebraic reformulation + local branch data; no global claim, no Groebner')
    (HERE / 'r20_tc_poly.json').write_text(json.dumps(out, indent=1, default=str))
    print()
    print('saved r20_tc_poly.json')


if __name__ == '__main__':
    main()
