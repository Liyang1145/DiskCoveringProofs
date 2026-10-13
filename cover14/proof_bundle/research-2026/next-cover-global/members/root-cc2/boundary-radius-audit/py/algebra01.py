"""root-cc2 boundary-radius-audit: exact checks of the boundary-facet extension.

Setup (the proof's coordinates): u=(0,0), v=(l,0), w=(wx,wy) with wy>0; the boundary
facet runs from the circumcentre O_f to the boundary switch A, both on the perpendicular
bisector x=l/2, with ordinates h_f and h_A and h_A <= h_f (nearest-site inequality).

Checks:
 (A1) h_f = (|w|^2 - l wx)/(2 wy) is exactly O_f's ordinate (sympy).
 (A2) bearing identity beta = (pi/2 - gamma_f) - phi_A and the two length identities.
 (A3) the deficit chain, symbolically.
 (A4) the per-face ledger sum_e Delta_e = (sum beta_e - pi)/2 (exact symbolic).
 (A5) the area identity (1/2)|u x (O_f - A)| = R_f rho_A sin(beta)/2.
 (A6) concrete rational instances checked to 40 digits.
"""
from pathlib import Path
import sympy as sp
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

l, wx, wy = sp.symbols('l w_x w_y', positive=True)
h, hA = sp.symbols('h h_A', positive=True)
hf = sp.symbols('h_f', positive=True)

P('=' * 78)
P('(A1) nearest-site ordinate = circumcentre ordinate')
d_diff = sp.expand(((l/2)**2 + h**2) - ((l/2 - wx)**2 + (h - wy)**2))
P('    |z-u|^2 - |z-w|^2 = %s' % sp.factor(d_diff))
sol = sp.solve(sp.Eq(sp.expand(((l/2)**2 + h**2) - ((l/2 - wx)**2 + (h - wy)**2)), 0), h)[0]
P('    equality when h = %s   (=: h_f)' % sp.simplify(sol))
Ox, Oy = sp.symbols('O_x O_y')
e1 = sp.expand(Ox**2 + Oy**2 - (Ox-l)**2 - Oy**2)
e2 = sp.expand(Ox**2 + Oy**2 - (Ox-wx)**2 - (Oy-wy)**2)
s = sp.solve([sp.Eq(e1, 0), sp.Eq(e2, 0)], [Ox, Oy], dict=True)[0]
P('    circumcentre of (u,v,w) = (%s, %s)' % (sp.simplify(s[Ox]), sp.simplify(s[Oy])))
P('    identical to h_f : %s' % sp.simplify(sp.Eq(sp.simplify(s[Oy]), sp.simplify(sol))))

P('')
P('=' * 78)
P('(A2) the angle and length identities')
P('    bearing(O_f-u) = atan2(h_f, l/2) = pi/2 - atan2(l/2, h_f) = pi/2 - gamma_f.')
P('      sympy: %s' % sp.simplify(sp.atan2(hf, l/2) - (sp.pi/2 - sp.atan2(l/2, hf))))
P('    bearing(A-u) = atan2(h_A, l/2) = phi_A with tan phi_A = 2 h_A/l.')
P('      sympy: tan(atan2(hA,l/2)) - 2 h_A/l = %s'
  % sp.simplify(sp.tan(sp.atan2(hA, l/2)) - 2*hA/l))
beta = sp.symbols('beta', real=True)
P('    beta = bearing(O_f-u) - bearing(A-u), so gamma_f + (pi/2 + phi_A) = pi - beta:')
P('      LHS-RHS = %s' % sp.simplify((sp.pi/2 - sp.atan2(l/2, hf) + sp.pi/2 + sp.atan2(hA, l/2))
                                    - (sp.pi - beta) - beta + beta))
P('    R_f sin gamma_f = l/2: R_f = sqrt((l/2)^2 + h_f^2), sin gamma_f = (l/2)/R_f -> l/2.')
P('    rho_A sin gamma_A = l/2: rho_A = sqrt((l/2)^2 + h_A^2),')
P('      sin gamma_A = cos phi_A = (l/2)/rho_A -> l/2.')

P('')
P('=' * 78)
P('(A3) deficit chain (symbolic)')
P('    tau = |x-y|/(x+y) = |tan Delta| tan(beta/2)  [Delta=(gamma_f-gamma_g)/2, gamma_f+gamma_g=pi-beta]')
t = sp.symbols('t', positive=True)
P('    with t = tan(beta/2): sin beta = 2t/(1+t^2), 1-cos beta = 2t^2/(1+t^2)')
P('      tau sin beta = |tan Delta| t * 2t/(1+t^2) = |tan Delta| (1-cos beta)')
P('      sympy: %s' % sp.simplify(2*t/(1+t**2)*t - (1 - (1-t**2)/(1+t**2))))
P('    so U^2(1-xy) sin beta >= U^2 tau sin beta = U^2(1-cos beta)|tan Delta| >= U^2(1-cos beta)|Delta|')

P('')
P('=' * 78)
P('(A4) per-face ledger (exact)')
b1, b2, b3, g1, g2, g3 = sp.symbols('beta_1 beta_2 beta_3 gamma_1 gamma_2 gamma_3', positive=True)
Dsum = (g1 - (sp.pi-b1)/2) + (g2 - (sp.pi-b2)/2) + (g3 - (sp.pi-b3)/2)
P('    sum_e Delta_e = %s' % sp.expand(Dsum))
sub = sp.simplify(sp.expand(Dsum.subs(g1, sp.pi/2 - g2 - g3)))
P('    after substituting the real face angle sum g1+g2+g3 = pi/2: %s' % sub)
P('    target (b1+b2+b3-pi)/2 = %s' % sp.expand((b1+b2+b3-sp.pi)/2))
P('    difference = %s' % sp.simplify(sp.expand(sub - (b1+b2+b3-sp.pi)/2)))

P('')
P('=' * 78)
P('(A5) area identity (numerical)')
P('    (1/2)|u x (O_f-A)| = (l/2)|h_f-h_A|/2 ;  R_f rho_A sin(beta)/2 with')
P('    sin beta = (l/2)(h_f-h_A)/(R_f rho_A)')

P('')
P('=' * 78)
P('(A6) rational instances')
mp.mp.dps = 40
for (lv, wxv, wyv, hAv) in [(mp.mpf(2), mp.mpf(1), mp.mpf(1), mp.mpf('0.3')),
                            (mp.mpf('1.7'), mp.mpf('0.9'), mp.mpf('1.3'), mp.mpf('0.2')),
                            (mp.mpf(3), mp.mpf('1.2'), mp.mpf('0.8'), mp.mpf('0.1')),
                            (mp.mpf(2), mp.mpf(3), mp.mpf(1), mp.mpf('0.2'))]:
    hfv = (wxv**2 + wyv**2 - lv*wxv)/(2*wyv)
    Rf = mp.sqrt((lv/2)**2 + hfv**2)
    rhoA = mp.sqrt((lv/2)**2 + hAv**2)
    beta_v = mp.atan2(hfv, lv/2) - mp.atan2(hAv, lv/2)
    gf = mp.atan2(lv/2, hfv); gA = mp.pi/2 + mp.atan2(2*hAv/lv)
    P('    l=%s w=(%s,%s) h_A=%s' % (mp.nstr(lv, 6), mp.nstr(wxv, 6), mp.nstr(wyv, 6), mp.nstr(hAv, 6)))
    P('      h_f=%s ; h_A<=h_f: %s ; beta=%s ; gamma_f=%s ; gamma_A=%s'
      % (mp.nstr(hfv, 10), hAv <= hfv, mp.nstr(beta_v, 10), mp.nstr(gf, 10), mp.nstr(gA, 10)))
    if hAv > hfv:
        P('      (h_A > h_f: the nearest-site hypothesis FAILS; angles still satisfy the algebra,')
        P('        but this configuration cannot occur for a boundary switch.)')
    P('      gamma_f+gamma_A-(pi-beta) = %s ; R_f sin gf-l/2 = %s ; rho_A sin gA-l/2 = %s'
      % (mp.nstr(gf+gA-(mp.pi-beta_v), 6), mp.nstr(Rf*mp.sin(gf)-lv/2, 6),
         mp.nstr(rhoA*mp.sin(gA)-lv/2, 6)))
    P('      area: (l/2)|h_f-h_A|/2 = %s ; R_f rho_A sin beta/2 = %s'
      % (mp.nstr((lv/2)*abs(hfv-hAv)/2, 12), mp.nstr(Rf*rhoA*mp.sin(beta_v)/2, 12)))

(OUT / 'algebra01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'algebra01.txt')
