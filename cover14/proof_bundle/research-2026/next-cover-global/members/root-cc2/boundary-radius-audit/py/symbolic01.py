"""root-cc2 boundary-radius-audit: SYMBOLIC re-derivation of the disputed points.

This file replaces the earlier symbolic01.py in the same directory; every statement below
is symbolic (no examples used as evidence).  Corrections applied: the xy inequality
direction, the ledger form, the area expression, the pack factors, the limit endpoint.
"""
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

wx, wy, hA = sp.symbols('w_x w_y h_A', real=True)
wy = sp.symbols('w_y', positive=True)
l = sp.symbols('l', positive=True)
h = sp.symbols('h', real=True)
hf = sp.symbols('h_f', real=True)

P('=' * 78)
P('(1) nearest-site inequality: h_A <= h_f')
d = sp.expand(((l/2)**2 + h**2) - ((l/2-wx)**2 + (h-wy)**2))
P('  |z-u|^2 - |z-w|^2 = %s' % d)
P('  = 2 h w_y + l w_x - w_x^2 - w_y^2  =>  h <= (w_x^2+w_y^2-l w_x)/(2 w_y) = h_f')
P('  h_f = 0  <=>  w_x^2+w_y^2 = l w_x  <=>  (u-w).(v-w) = 0 : right triangle at w,')
P('  NOT w on the line uv (that would need w_y = 0).')
P('  phi_A = atan(2 h_A/l) in (-pi/2, pi/2);  gamma_A = pi/2 + phi_A in (0, pi).')

P('')
P('=' * 78)
P('(2) ledger with gamma_fe = the REAL opposite interior angle of triangle f')
g1, g2, g3, b1, b2, b3 = sp.symbols('gamma_1 gamma_2 gamma_3 beta_1 beta_2 beta_3', real=True)
Dsum = (g1-(sp.pi-b1)/2) + (g2-(sp.pi-b2)/2) + (g3-(sp.pi-b3)/2)
P('  sum_e Delta_fe = %s' % sp.expand(Dsum))
P('  under sum_e gamma_fe = pi: %s' % sp.expand(Dsum.subs(g1, sp.pi-g2-g3)))
P('  target (sum beta - pi)/2   : %s' % sp.expand((b1+b2+b3-sp.pi)/2))
P('  difference under sum gamma = pi: %s'
  % sp.simplify(sp.expand(Dsum.subs(g1, sp.pi-g2-g3) - (b1+b2+b3-sp.pi)/2)))
P('  => ledger = (sum_e beta_e - pi)/2, from the real face angle sum alone.')

P('')
P('=' * 78)
P('(3) the xy inequality, in the direction the deficit chain needs')
x, y, tau, M, m = sp.symbols('x y tau M m', positive=True)
P('  tau = |x-y|/(x+y);  M = max(x,y) <= 1, m = min(x,y):')
P('    x y = M m = (m/M) M^2 <= m/M = (1-tau)/(1+tau)      [M^2 <= 1]')
P('  hence  1 - x y >= 1 - (1-tau)/(1+tau) = 2 tau/(1+tau) >= tau')
P('    sympy: 1-(1-tau)/(1+tau)-2tau/(1+tau) = %s'
  % sp.simplify(1-(1-tau)/(1+tau)-2*tau/(1+tau)))
P('  sanity: x = y = 1/2 => tau = 0, xy = 1/4 <= (1-0)/(1+0) = 1 (strict), consistent with')
P('    xy <= (1-tau)/(1+tau); the reverse inequality would give xy >= 1, false.')
P('  deficit chain:')
P('    D_e = U^2(1-xy) sin beta >= U^2 (2tau/(1+tau)) sin beta >= U^2 tau sin beta')
P('        = U^2 (1-cos beta)|tan Delta| >= U^2 (1-cos beta)|Delta|')
P('    with t = tan(beta/2): sin beta = 2t/(1+t^2), 1-cos beta = 2t^2/(1+t^2), so')
P('    tau sin beta = |tan Delta| tan(beta/2) sin beta = |tan Delta| (1-cos beta).')

P('')
P('=' * 78)
P('(4) paired facet area: cross(O_f-u, A-u)')
P('  O_f-u = (l/2, h_f), A-u = (l/2, h_A) (both on the perpendicular bisector x = l/2)')
P('  cross = (l/2) h_A - h_f (l/2) = l (h_A - h_f)/2   (sympy: %s)'
  % sp.factor((l/2)*hA - hf*(l/2)))
P('  |cross|/2 = (l/2)|h_f-h_A|/2;  sin beta = |cross|/(R_f rho_A) with')
P('  R_f = sqrt((l/2)^2+h_f^2), rho_A = sqrt((l/2)^2+h_A^2), so')
P('  R_f rho_A sin beta = (l/2)|h_f-h_A| = 2 * area(u, O_f, A).')
P('  (u x (A - O_f) with u = 0 is identically zero - not the area expression.)')

P('')
P('=' * 78)
P('(5) packing factors')
P('  single face:        D_f >= (U^2/2) m_f |sum_e beta_e - pi|')
P('  all faces summed:   >= (U^2/4) sum_f m_f |...|   (each interior edge counted twice)')
P('  edge-disjoint pack: >= (U^2/2) sum_{f in pack} m_f |...|  (no shared edges inside)')

P('')
P('=' * 78)
P('(6) compact limit')
P('  Take the constant-graph subsequence as eps -> 0 first; at finite eps we use only')
P('  that the configuration is a cover at radius rho_eps (rho_eps may EXCEED r, and no')
P('  relation rho_eps <= U is used).  Only at the limit endpoint do we use')
P('  rho_A <= r <= U, and the deficit expression U^2(1-xy)sin beta is continuous there.')



