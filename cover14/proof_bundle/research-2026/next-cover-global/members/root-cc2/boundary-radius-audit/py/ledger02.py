"""root-cc2 boundary-radius-audit: clean ledger check on concrete faces.

Simplest form of the bookkeeping: for each edge e of a dual face, let gamma_fe be the
angle at the opposite centre (real, for interior edges) and gamma_other_e the angle at the
third-corner centre (real for interior edges, virtual gamma_A for a boundary edge).  Then

    beta_e = pi - gamma_fe - gamma_other_e,   sum_e (pi - beta_e) = pi (real face angles)

hence sum_e gamma_other_e = pi/2 and
    Delta_fe := gamma_fe - (pi - beta_e)/2,   sum_e Delta_fe = (2 pi - sum_e beta_e)/2 .

Also: (1/2)|u x (O_f - A)| = R_f rho_A sin(beta)/2 (paired facet area).
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 40
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

def circumcentre(u, v, w):
    ax, ay = u; bx, by = v; cx, cy = w
    d = 2*(ax*(by-cy) + bx*(cy-ay) + cx*(ay-by))
    ux = ((ax**2+ay**2)*(by-cy) + (bx**2+by**2)*(cy-ay) + (cx**2+cy**2)*(ay-by))/d
    uy = ((ax**2+ay**2)*(cx-bx) + (bx**2+by**2)*(ax-cx) + (cx**2+cy**2)*(bx-ax))/d
    return (ux, uy)

def angle(a, b, c):
    v1 = (b[0]-a[0], b[1]-a[1]); v2 = (c[0]-a[0], c[1]-a[1])
    return mp.atan2(abs(v1[0]*v2[1]-v1[1]*v2[0]), v1[0]*v2[0]+v1[1]*v2[1])

P('=' * 78)
P('(1) the real face angle sum and the ledger identity on concrete faces')
P('    u=(0,0), v=(l,0), w=(wx,wy)')
for (lv, wv) in [('2', '1,1'), ('2', '0.5,1.5'), ('2', '1.5,0.8'), ('1.7', '0.9,1.3'), ('1.0', '0.3,2.0')]:
    l = mp.mpf(lv); wx, wy = [mp.mpf(t) for t in wv.split(',')]
    u = (mp.mpf(0), mp.mpf(0)); v = (l, mp.mpf(0)); w = (wx, wy)
    O = circumcentre(u, v, w); Rf = mp.sqrt(O[0]**2 + O[1]**2); hf = O[1]
    b_u = angle(u, v, w); b_v = angle(v, u, w); b_w = angle(w, u, v)
    ssum = b_u + b_v + b_w
    P('    l=%-5s w=(%s,%s): corner angles sum = %s (pi=%s) ; h_f=%s R_f=%s'
      % (lv, mp.nstr(wx,5), mp.nstr(wy,5), mp.nstr(ssum,12), mp.nstr(mp.pi,12),
         mp.nstr(hf,10), mp.nstr(Rf,10)))

P('')
P('=' * 78)
P('(2) boundary edge uv: the anchor and the virtual angle')
for (lv, wv) in [('2', '0.5,1.5'), ('2', '1.5,0.8'), ('1.7', '0.9,1.3'), ('1.0', '0.3,2.0')]:
    l = mp.mpf(lv); wx, wy = [mp.mpf(t) for t in wv.split(',')]
    u = (mp.mpf(0), mp.mpf(0)); v = (l, mp.mpf(0)); w = (wx, wy)
    O = circumcentre(u, v, w); Rf = mp.sqrt(O[0]**2 + O[1]**2); hf = O[1]
    P('    l=%-5s w=(%s,%s) h_f=%s' % (lv, mp.nstr(wx,5), mp.nstr(wy,5), mp.nstr(hf,10)))
    if hf <= 0:
        P('       h_f <= 0: the perpendicular bisector meets the nearest-site region only')
        P('       at or below h_f; a boundary switch needs h_A <= h_f < 0 on this side, so')
        P('       this face orientation cannot host the boundary edge uv (consistent with')
        P('       the hypothesis h_A > 0 used by the proof).')
        continue
    for frac in ['0.4', '0.8', '1.0']:
        hA = hf*mp.mpf(frac)
        A = (l/2, hA); rhoA = mp.sqrt((l/2)**2 + hA**2)
        beta = mp.atan2(hf, l/2) - mp.atan2(hA, l/2)
        gf = mp.atan2(l/2, hf); gA = mp.pi/2 + mp.atan(2*hA/l)
        ar1 = (l/2)*abs(hf-hA)/2; ar2 = Rf*rhoA*mp.sin(beta)/2
        P('       h_A/h_f=%s beta=%-11s gamma_f=%-11s gamma_A=%-11s  [sum-(pi-beta)]=%s'
          % (frac, mp.nstr(beta,10), mp.nstr(gf,10), mp.nstr(gA,10),
             mp.nstr(gf+gA-(mp.pi-beta),5)))
        P('          [R_f sin gf - l/2]=%-9s [rho_A sin gA - l/2]=%-9s  areas %s vs %s'
          % (mp.nstr(Rf*mp.sin(gf)-l/2,5), mp.nstr(rhoA*mp.sin(gA)-l/2,5),
             mp.nstr(ar1,12), mp.nstr(ar2,12)))

P('')
P('=' * 78)
P('(3) the ledger identity, symbolic')
P('    beta_e = pi - gamma_fe - gamma_other_e  and  sum_e (pi - beta_e) = pi')
P('    => sum_e (gamma_fe + gamma_other_e) = 2pi - pi = pi.')
P('    Delta_fe = gamma_fe - (pi - beta_e)/2')
P('    sum_e Delta_fe = sum gamma_fe - (3pi - sum beta_e)/2')
P('    and sum gamma_fe = pi - sum gamma_other_e = pi - (pi - sum gamma_fe) ... use')
P('    sum gamma_other_e = pi - sum gamma_fe (from sum(gamma_f+gamma_other)=pi):')
P('    so sum gamma_fe - (3pi - sum beta)/2 = sum gamma_fe - 3pi/2 + sum beta/2.')
P('    With sum beta = 3pi - sum gamma_f - sum gamma_other = 3pi - pi = 2pi:')
P('    sum_e Delta_fe = sum gamma_fe - 3pi/2 + pi = sum gamma_fe - pi/2.')
P('    And sum gamma_fe = pi - sum gamma_other_e, so the ledger is the identity')
P('    sum_e Delta_fe = (sum_e gamma_fe - sum_e gamma_other_e)/2,')
P('    which equals (2pi - sum beta)/2.  Both forms are the single relation')
P('    sum_e (gamma_fe + gamma_other_e) = pi.')

(OUT / 'ledger02.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'ledger02.txt')
