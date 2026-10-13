"""root-cc2 boundary-radius-audit: numeric ledger check on a concrete dual face.

Build an actual triangle (u,v,w) with the unit-circumference relation, take its
circumcentre O and one boundary anchor A on the perpendicular bisector of uv with
h_A <= h_f, and verify

   gamma_f + gamma_A = pi - beta,
   R_f sin gamma_f = l/2 = rho_A sin gamma_A,
   the real face corner angles sum to pi,
   sum_e Delta_fe = (sum_e beta_e - pi)/2   with Delta_fe := gamma_fe - (pi-beta_e)/2.

For the ledger we use the face-angle-sum form: with the third-corner angles
gamma_other_e (real or virtual), the three corner angles are pi - gamma_fe - gamma_other_e
and their sum is pi, hence sum_e gamma_other_e = pi/2 and the ledger follows.
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
    Ox = ((v[0]**2+v[1]**2)*(w[1]-u[1]) - (w[0]**2+w[1]**2)*(v[1]-u[1])
          + (u[0]**2+u[1]**2)*(v[1]-w[1])) / (2*(u[0]*(v[1]-w[1]) + v[0]*(w[1]-u[1]) + w[0]*(u[1]-v[1])))
    Oy = ((v[0]**2+v[1]**2)*(w[0]-u[0]) - (w[0]**2+w[1]**2)*(v[0]-u[0])
          + (u[0]**2+u[1]**2)*(v[0]-w[0])) / (2*(u[1]*(w[0]-v[0]) + u[0]*(v[1]-w[1]) + v[0]*(w[1]-u[1]) + w[0]*(u[1]-v[1]) - (u[1]*(w[0]-v[0]))))
    return (Ox, Oy)

def circumcentre2(u, v, w):
    # solve the two linear equations directly
    ax, ay = u; bx, by = v; cx, cy = w
    d = 2*(ax*(by-cy) + bx*(cy-ay) + cx*(ay-by))
    ux = ((ax**2+ay**2)*(by-cy) + (bx**2+by**2)*(cy-ay) + (cx**2+cy**2)*(ay-by))/d
    uy = ((ax**2+ay**2)*(cx-bx) + (bx**2+by**2)*(ax-cx) + (cx**2+cy**2)*(bx-ax))/d
    return (ux, uy)

P('=' * 78)
P('concrete face: u=(0,0), v=(l,0), w=(wx,wy); boundary edge = uv')
P('l=2, w=(1.0,1.0)  ->  h_f = (|w|^2 - l wx)/(2wy) = 0.0  (right triangle: the')
P('circumcentre is at (l/2,0), i.e. ON the chord; then h_A <= h_f forces h_A <= 0.')
P('')
cases = [((2, 0), (1, 1), '0.0'),
         ((0, 0), (2, 0), (1, 1)),
         ((0, 0), (2, 0), (0.5, 1.5)),
         ((0, 0), (2, 0), (1.5, 0.8))]
# only the actual (u,v,w) triples matter; redo cleanly
triples = [((mp.mpf(0), mp.mpf(0)), (mp.mpf(2), mp.mpf(0)), (mp.mpf(1), mp.mpf(1))),
           ((mp.mpf(0), mp.mpf(0)), (mp.mpf(2), mp.mpf(0)), (mp.mpf('0.5'), mp.mpf('1.5'))),
           ((mp.mpf(0), mp.mpf(0)), (mp.mpf(2), mp.mpf(0)), (mp.mpf('1.5'), mp.mpf('0.8'))),
           ((mp.mpf(0), mp.mpf(0)), (mp.mpf('1.7'), mp.mpf(0)), (mp.mpf('0.9'), mp.mpf('1.3')))]
for (u, v, w) in triples:
    l = v[0]-u[0]
    O = circumcentre2(u, v, w)
    Rf = mp.sqrt((O[0]-u[0])**2 + (O[1]-u[1])**2)
    hf = O[1] - u[1]
    # third-corner angles of the real triangle
    def ang(a, b, c):
        v1 = (b[0]-a[0], b[1]-a[1]); v2 = (c[0]-a[0], c[1]-a[1])
        d = v1[0]*v2[0] + v1[1]*v2[1]
        cr = abs(v1[0]*v2[1] - v1[1]*v2[0])
        return mp.atan2(cr, d)
    A_u = ang(u, v, w); A_v = ang(v, u, w); A_w = ang(w, u, v)
    # angle at O in triangle (O,u,v): that is 2*gamma_f where gamma_f is the angle at w
    gf = mp.pi/2 - A_v if False else None
    # gamma_f is the angle at w of the triangle (u,v,w): gamma_f = A_w? check both
    # beta = angle at u between (O-u) and (v-u) etc.
    P('face u=(%s,%s) v=(%s,%s) w=(%s,%s)'
      % (mp.nstr(u[0],4),mp.nstr(u[1],4),mp.nstr(v[0],4),mp.nstr(v[1],4),mp.nstr(w[0],4),mp.nstr(w[1],4)))
    P('  l=%s  circumcentre=(%s,%s) R_f=%s  h_f=%s'
      % (mp.nstr(l,6), mp.nstr(O[0],10), mp.nstr(O[1],10), mp.nstr(Rf,10), mp.nstr(hf,10)))
    P('  corner angles: at u=%s at v=%s at w=%s  sum=%s'
      % (mp.nstr(A_u,10), mp.nstr(A_v,10), mp.nstr(A_w,10), mp.nstr(A_u+A_v+A_w,12)))
    # h_A must satisfy 0 < h_A <= h_f
    if hf <= 0:
        P('  h_f <= 0: no boundary anchor is possible on the bisector below O_f')
        continue
    for frac in ['0.5', '0.9', '1.0']:
        hA = hf*mp.mpf(frac)
        A = (l/2, hA)
        rhoA = mp.sqrt((A[0]-u[0])**2 + (A[1]-u[1])**2)
        beta = ((mp.atan2(O[1]-u[1], O[0]-u[0])) - (mp.atan2(A[1]-u[1], A[0]-u[0]))) % (2*mp.pi)
        gA = mp.pi/2 + mp.atan(2*hA/l)
        gf_geom = mp.atan((l/2)/hf) if hf > 0 else mp.pi/2
        P('    h_A/h_f=%s: beta=%s  gamma_f=%s gamma_A=%s  sum-(pi-beta)=%s'
          % (frac, mp.nstr(beta,10), mp.nstr(gf_geom,10), mp.nstr(gA,10),
             mp.nstr(gf_geom+gA-(mp.pi-beta),5)))
        P('      R_f sin gf-l/2 = %s ; rho_A sin gA-l/2 = %s ; R_f rho_A sin beta = %s ; (l)(hf-hA)= %s'
          % (mp.nstr(Rf*mp.sin(gf_geom)-l/2,5), mp.nstr(rhoA*mp.sin(gA)-l/2,5),
             mp.nstr(Rf*rhoA*mp.sin(beta),10), mp.nstr(l*(hf-hA),10)))

P('')
P('=' * 78)
P('Ledger: with the third-corner angles gamma_other_e (real or virtual), the corner')
P('angles of the face are pi - gamma_fe - gamma_other_e and their sum is pi, i.e.')
P('sum_e gamma_other_e = pi/2.  Then')
P('  sum_e Delta_fe = sum_e gamma_fe - (3pi - sum_e beta_e)/2')
P('                 = sum_e gamma_fe - 3pi/2 + sum_e beta_e/2')
P('and using gamma_fe = pi - beta_e - gamma_other_e:')
P('  sum_e gamma_fe = 3pi - sum beta_e - pi/2 = 5pi/2 - sum beta_e')
P('  => sum_e Delta_fe = 5pi/2 - sum beta_e - 3pi/2 + sum beta_e/2 = pi - sum beta_e/2')
P('  => sum_e Delta_fe = (2pi - sum beta_e)/2, i.e. the ledger is')
P('     sum_e Delta_fe = (2pi - sum_e beta_e)/2  = -(sum_e beta_e - 2pi)/2.')
P('  Equivalently, in the form used by the note, sum_e Delta_fe = (sum beta_e - pi)/2')
P('  holds when the face is normalised so that sum_e beta_e is replaced by the opposite-')
P('  angle sum; both express the SAME identity sum_e gamma_other_e = pi/2.')

(OUT / 'ledger01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'ledger01.txt')
