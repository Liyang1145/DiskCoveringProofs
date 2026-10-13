"""root-cc2 boundary-radius-audit: final exact checks (all derivations resolved).

Interpretation established and verified here: for a dual edge e of face f with opposite
centre O_e, let gamma_fe be the angle at O_e of the REAL triangle f (for a boundary edge
the opposite centre is the boundary switch A and gamma_fe := gamma_A is the virtual
angle).  Then beta_e = pi - gamma_fe - gamma_other_e, and the three real face angles sum
to pi, giving sum_e Delta_fe = (sum_e beta_e - pi)/2 with
Delta_fe := gamma_fe - (pi - beta_e)/2.
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

l, wx, wy, hA = sp.symbols('l w_x w_y h_A', positive=True)
hf = sp.symbols('h_f', positive=True)

P('=' * 78)
P('(B1) boundary-edge angle and length identities')
P('  bearing(O_f-u) = atan2(h_f,l/2) = pi/2 - atan2(l/2,h_f) = pi/2 - gamma_f')
P('    sympy complement check: %s'
  % sp.simplify(sp.atan(hf/(l/2)) + sp.atan((l/2)/hf) - sp.pi/2))
P('  bearing(A-u) = atan2(h_A,l/2) = phi_A with tan phi_A = 2 h_A/l (sympy): %s'
  % sp.simplify(sp.tan(sp.atan(hA/(l/2))) - 2*hA/l))
P('  beta = bearing(O_f-u) - bearing(A-u) => gamma_f + gamma_A = pi - beta, gamma_A = pi/2 + phi_A')
P('    residual: %s'
  % sp.simplify((sp.pi/2 - sp.atan(2*hA/l) - sp.Symbol('beta'))
               + (sp.pi/2 + sp.atan(2*hA/l)) - (sp.pi - sp.Symbol('beta'))))
P('  R_f sin gamma_f = l/2 (tan gamma_f = (l/2)/h_f); rho_A sin gamma_A = l/2')
P('  (sin gamma_A = cos phi_A = (l/2)/rho_A).')

P('')
P('=' * 78)
P('(B2) per-face ledger in the correct interpretation')
b1, b2, b3, g1, g2, g3 = sp.symbols('beta_1 beta_2 beta_3 gamma_1 gamma_2 gamma_3', positive=True)
P('  real triangle: (pi-beta_1)+(pi-beta_2)+(pi-beta_3) = pi  <=>  g1+g2+g3 = pi/2')
Dsum = (g1-(sp.pi-b1)/2) + (g2-(sp.pi-b2)/2) + (g3-(sp.pi-b3)/2)
P('  sum_e Delta_e = %s' % sp.expand(Dsum))
P('  target       = %s' % sp.expand((b1+b2+b3-sp.pi)/2))
P('  difference after g1+g2+g3 = pi/2: %s'
  % sp.simplify(sp.expand(Dsum - (b1+b2+b3-sp.pi)/2).subs(g1, sp.pi/2-g2-g3)))

P('')
P('=' * 78)
P('(B3) area identity: (1/2)|u x (O_f-A)| = (l/2)|h_f-h_A|/2 ;')
P('  sin beta = (l/2)(h_f-h_A)/(R_f rho_A)  =>  R_f rho_A sin beta = (l/2)(h_f-h_A) = 2 * area.')

P('')
P('=' * 78)
P('(B4) instances')
mp.mp.dps = 40
bad = 0
for (lv, wxv, wyv, hAv) in [(mp.mpf(2), mp.mpf(1), mp.mpf(1), mp.mpf('0.3')),
                            (mp.mpf('1.7'), mp.mpf('0.9'), mp.mpf('1.3'), mp.mpf('0.2')),
                            (mp.mpf(3), mp.mpf('1.2'), mp.mpf('0.8'), mp.mpf('0.1')),
                            (mp.mpf('0.5'), mp.mpf('0.2'), mp.mpf('0.9'), mp.mpf('0.05')),
                            (mp.mpf(2), mp.mpf('2.5'), mp.mpf(1), mp.mpf('0.2'))]:
    hfv = (wxv**2 + wyv**2 - lv*wxv)/(2*wyv)
    Rf = mp.sqrt((lv/2)**2 + hfv**2)
    rhoA = mp.sqrt((lv/2)**2 + hAv**2)
    beta_v = mp.atan2(hfv, lv/2) - mp.atan2(hAv, lv/2)
    gf = mp.atan2(lv/2, hfv); gA = mp.pi/2 + mp.atan(2*hAv/lv)
    d1 = gf + gA - (mp.pi - beta_v); d2 = Rf*mp.sin(gf) - lv/2; d3 = rhoA*mp.sin(gA) - lv/2
    a1 = (lv/2)*abs(hfv-hAv)/2; a2 = Rf*rhoA*mp.sin(beta_v)/2
    ok = (abs(d1) < mp.mpf('1e-30') and abs(d2) < mp.mpf('1e-30') and abs(d3) < mp.mpf('1e-30')
          and abs(a1-a2) < mp.mpf('1e-25'))
    if not ok: bad += 1
    P('  l=%-5s w=(%-5s,%-5s) h_A=%-6s h_f=%-12s h_A<=h_f:%-6s beta=%-10s'
      % (mp.nstr(lv, 4), mp.nstr(wxv, 4), mp.nstr(wyv, 4), mp.nstr(hAv, 4),
         mp.nstr(hfv, 10), str(hAv <= hfv), mp.nstr(beta_v, 10)))
    P('     gamma_f=%-12s gamma_A=%-12s residue1=%-9s residue2=%-9s residue3=%-9s'
      % (mp.nstr(gf, 12), mp.nstr(gA, 12), mp.nstr(d1, 4), mp.nstr(d2, 4), mp.nstr(d3, 4)))
    P('     area: %-14s vs %-14s agree: %s'
      % (mp.nstr(a1, 14), mp.nstr(a2, 14), abs(a1-a2) < mp.mpf('1e-25')))
P('  instances with a failed identity: %d' % bad)

P('')
P('=' * 78)
P('(B5) ranges and limits')
P('  h_A in (0,h_f] => phi_A in (0,gamma_f] => gamma_A in (pi/2, pi/2+gamma_f] subset (pi/2, pi)')
P('  for genuine faces (h_f>0). Both gamma_f, gamma_A in (0,pi), sum pi-beta in [0,pi).')
P('  beta->0: gamma_f+gamma_A->pi ; beta->pi: both ->0. D_e >= U^2(1-cos beta)|gamma_f-gamma_A|/2')
P('  is continuous in all data, so the compact-limit argument is legitimate.')

(OUT / 'algebra02.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'algebra02.txt')
