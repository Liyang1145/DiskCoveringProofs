"""Step 10: the TRUE low-dimensional exact system of the C182 candidate + numeric root.

Structure (verified): 4 orbits of 3 under the exact 120-deg rotation.
  hub   A : {0,1,2}  norm a, angles 0, 120, 240 (deg, relative to c_0)
  mid   B : {3,4,5}  norm t, angles 60, 180, 300
  high  C : {6,8,9}  norm b, angles  gamma-20, gamma+100, gamma+220   (gamma = theta_6 - theta_0)
  high  D : {7,10,11} norm b, angles  beta+180, beta+300, beta+60     (beta = theta_7 - theta_0 - 180, negative)
R_D attained at two hole families:
  u2 = circ(c_0,c_6,c_7)   |u2| = a + R
  u3 = circ(c_0,c_1,c_3)   |u3| = t - R
Equations (exact, analytic; all trig of multiples of 120 deg is rational):
  (E1) |c_6-c_0|^2 = |c_7-c_0|^2            (hole bisector: u2 on ray theta_0)
  (E2) |u2-c_0|=R with |u2| = a+R            (hole at distance R)
  (E3) |u3-c_0|=R with |u3| = t-R            (hole at distance R)
  (E4) |c_6-c_7|^2 = ... (radical axis closure)  [provided by E1+E2]
  (E5) u3 = circ(c_0,c_1,c_3), value R
"""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
Am = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in A["centers_dec17"]]
rad = [mp.sqrt(c[0]**2+c[1]**2) for c in Am]
ang = [mp.atan2(c[1], c[0]) for c in Am]
phi0 = ang[0]
OUT = []
def W(s=""): OUT.append(str(s))

# measured relative angles (deg)
rel = [mp.fmod((ang[i]-phi0)*180/mp.pi+360, 360) for i in range(12)]
W("### measured relative angles (deg) and norms (dps=50)")
for i in range(12):
    W(f"  c{i:2d}: rel={mp.nstr(rel[i],26):<28} |c|={mp.nstr(rad[i],30)}")
beta = rel[7]-180          # ~ -20.891 deg
gamt = rel[6]              # ~ +20.891 deg  (theta_6)
W(f"\n  beta (c7 anchor)  = {mp.nstr(beta,26)} deg")
W(f"  gamma (c6 anchor) = {mp.nstr(gamt,26)} deg")
W(f"  beta + alpha?  =>  check whether beta = -(alpha) with alpha = (rel[6]) : "
  f"alpha+beta = {mp.nstr(gamt+beta,26)}")
W(f"  rel[3]-rel[0] = {mp.nstr(rel[3]-rel[0],26)}  (should be 60)")
W(f"  rel[6]-rel[3] = {mp.nstr(rel[6]-rel[3],26)}")
W(f"  rel[0]-rel[7] = {mp.nstr(rel[0]-rel[7]+360,26)}")

# ---- exact analytic construction: sites as functions of (a,t,b,al,be)
sq3 = mp.sqrt(3)
def R120(k):
    th = 2*mp.pi*k/3
    return (mp.cos(th), mp.sin(th))
def sites(a, t, b, al, be):
    """al = theta_6 relative to hub (deg), be = theta_7 relative (deg).
    hub angles: 0,120,240 ; mid: 60,180,300 ;
    C = {6,8,9} at al, al+120, al+240 ; D = {7,10,11} at be, be+120, be+240"""
    out = []
    for i in range(3):
        th = mp.pi*2*i/3
        out.append((a*mp.cos(th), a*mp.sin(th)))
    for i in range(3):
        th = mp.pi/3 + mp.pi*2*i/3
        out.append((t*mp.cos(th), t*mp.sin(th)))
    for i in range(3):
        th = al*mp.pi/180 + mp.pi*2*i/3
        out.append((b*mp.cos(th), b*mp.sin(th)))
    for i in range(3):
        th = be*mp.pi/180 + mp.pi*2*i/3
        out.append((b*mp.cos(th), b*mp.sin(th)))
    return out

def circ(p, q, r):
    ax, ay = p; bx, by = q; cx, cy = r
    d = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/d
    uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/d
    return (ux, uy)
def dist(p, q): return mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
def norm(p): return mp.sqrt(p[0]**2+p[1]**2)

# measured values as seed
a0, t0, b0 = rad[0], rad[3], rad[6]
al0, be0 = gamt, beta
R0 = mp.mpf("0.361102963744508672616920293903")
W("\n### residual check of the closure equations at the measured seed")
def residuals(a, t, b, al, be, R):
    S = sites(a, t, b, al, be)
    c0, c3, c6, c7 = S[0], S[3], S[6], S[7]
    # E1: |c6-c0| = |c7-c0|
    e1 = dist(c6, c0)**2 - dist(c7, c0)**2
    # E2: hole u2 = circ(c0,c6,c7); need |u2| = a+R and |u2-c0| = R
    u2 = circ(c0, c6, c7)
    e2 = norm(u2) - (a + R)
    e3 = dist(u2, c0) - R
    # E3: hole u3 = circ(c0,c1,c3); need |u3| = t-R and |u3-c0| = R
    u3 = circ(S[0], S[1], S[3])
    e4 = norm(u3) - (t - R)
    e5 = dist(u3, c0) - R
    return mp.matrix([e1, e2, e3, e4, e5]), (u2, u3)
r0, (u2, u3) = residuals(a0, t0, b0, al0, be0, R0)
W(f"  E1 = {mp.nstr(r0[0],10)}")
W(f"  E2 = |u2|-(a+R)   = {mp.nstr(r0[1],10)}")
W(f"  E3 = |u2-c0|-R    = {mp.nstr(r0[2],10)}")
W(f"  E4 = |u3|-(t-R)   = {mp.nstr(r0[3],10)}")
W(f"  E5 = |u3-c0|-R    = {mp.nstr(r0[4],10)}")
W("  (residuals ~1e-16 are the 17-digit literal rounding; the relations are exact in the ideal cfg)")

# ---- solve the 5 systems for (b, al, be) with (a,t,R) fixed, and for (a,t,b,al,be) with R fixed
W("\n### Newton solve: unknowns (a,t,b,al,be) with R fixed at the certified R_D")
def F(x):
    a, t, b, al, be = x
    r, _ = residuals(a, t, b, al, be, R0)
    return r
x = mp.matrix([a0, t0, b0, al0, be0])
try:
    xs = mp.findroot(lambda x: F(x), x, tol=mp.mpf('1e-40'), maxsteps=60)
    aS, tS, bS, alS, beS = [xs[i] for i in range(5)]
    W(f"  solution: a={mp.nstr(aS,32)}")
    W(f"            t={mp.nstr(tS,32)}")
    W(f"            b={mp.nstr(bS,32)}")
    W(f"            alpha={mp.nstr(alS,32)} deg")
    W(f"            beta ={mp.nstr(beS,32)} deg")
    rS, (u2S, u3S) = residuals(aS, tS, bS, alS, beS, R0)
    W(f"  residual max = {mp.nstr(max(abs(rS[i]) for i in range(5)),6)}")
    W(f"  |u2| = {mp.nstr(norm(u2S),32)}  a+R = {mp.nstr(aS+R0,32)}")
    W(f"  |u3| = {mp.nstr(norm(u3S),32)}  t-R = {mp.nstr(tS-R0,32)}")
    W(f"  alpha+beta = {mp.nstr(alS+beS,30)}   (180-alpha-beta = {mp.nstr(180-alS-beS,30)})")
    W(f"  the two high orbits' separation (alpha - beta) = {mp.nstr(alS-beS,30)} deg")
except Exception as ex:
    W(f"  findroot failed: {ex}")

# ---- Jacobian rank of the 5 equations in the 5 unknowns
W("\n### Jacobian rank of (E1..E5) w.r.t. (a,t,b,alpha,beta) at the measured seed")
J = mp.matrix(5, 5)
h = mp.mpf('1e-15')
x0 = [a0, t0, b0, al0, be0]
for k in range(5):
    xp = list(x0); xm = list(x0)
    xp[k] += h; xm[k] -= h
    rp, _ = residuals(*xp, R0)
    rm, _ = residuals(*xm, R0)
    for i in range(5):
        J[i, k] = (rp[i]-rm[i])/(2*h)
W(f"  J = {mp.nstr(J,8)}")
try:
    sv = mp.svd(J, compute_uv=False)
    W(f"  singular values: {[mp.nstr(s,10) for s in sv]}")
    W(f"  rank (rel tol 1e-20) = {sum(1 for s in sv if s > mp.mpf('1e-20')*sv[0])}")
except Exception as ex:
    W(f"  svd failed: {ex}")

(EV / "true_system.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
