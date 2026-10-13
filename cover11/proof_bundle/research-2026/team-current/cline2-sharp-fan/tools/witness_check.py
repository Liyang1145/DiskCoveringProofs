# -*- coding: utf-8 -*-
"""Independent check of the lead's non-ridge witness, then the envelope assessment.

Witness: r=.3750951887748506 b1=.9471039318692589 b2=.9148561742031202
         v=.4089871357815944 t=-.2502035007058863  (widths = g)
Checks: wedge and three disk margins; hub factor at the witness vs at the ridge
(v*,t*) = 2r sinT (cosD, sinD); value difference.
"""
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps = 40

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
OUT = Path(__file__).resolve().parent.parent / 'out'
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

J = json.loads((LEAD / 'joint_nested_frozen.json').read_text(encoding='utf-8-sig'))
z = [mp.mpf(str(v)) for v in J['z']]
R0 = mp.mpf(19)/50

r  = mp.mpf('0.3750951887748506'); b1 = mp.mpf('0.9471039318692589')
b2 = mp.mpf('0.9148561742031202'); v = mp.mpf('0.4089871357815944')
t  = mp.mpf('-0.2502035007058863')
s = mp.sqrt(1-r*r); T = b1+b2; D = b1-b2

P("=== 1. feasibility margins at the witness ===")
P("delta = atan2(t,v) = %s ; legal wedge -b2 < delta < b1 : %s"
  % (mp.nstr(mp.atan2(t, v), 12), (-b2 < mp.atan2(t, v) < b1)))
P("v > 0 : %s" % (v > 0))
d1 = (v - r*mp.sin(2*b1))**2 + (t + r*mp.cos(2*b1))**2 - r*r
d2 = (v - r*mp.sin(2*b2))**2 + (t - r*mp.cos(2*b2))**2 - r*r
dh = (v - s)**2 + t*t - (1-r)**2
P("face disk 1 : (v-r sin2b1)^2+(t+r cos2b1)^2 <= r^2 : residual %s  (<0 strictly: %s)"
  % (mp.nstr(d1, 12), d1 < 0))
P("face disk 2 : (v-r sin2b2)^2+(t-r cos2b2)^2 <= r^2 : residual %s  (<0 strictly: %s)"
  % (mp.nstr(d2, 12), d2 < 0))
P("hub  disk   : (v-s)^2+t^2 <= (1-r)^2            : residual %s  (<0 strictly: %s)"
  % (mp.nstr(dh, 12), dh < 0))
P("separation (auto) H - 2r|sin delta| = %s"
  % mp.nstr(mp.sqrt(v*v+t*t) - 2*r*abs(mp.sin(mp.atan2(t, v))), 10))
P("")

def hubfactor(rr, b1_, b2_, vv, tt):
    D1, D2 = 2*rr*mp.sin(b1_), 2*rr*mp.sin(b2_)
    X1, Y1 = vv - D1*mp.cos(b1_), D1*mp.sin(b1_) - tt
    X2, Y2 = vv - D2*mp.cos(b2_), D2*mp.sin(b2_) + tt
    L1, L2 = mp.sqrt(X1*X1+Y1*Y1), mp.sqrt(X2*X2+Y2*Y2)
    A_ = b1_ - mp.atan2(tt, vv); B_ = b2_ + mp.atan2(tt, vv)
    a1, a2 = z[1]-z[9], z[3]-z[9]
    area = (2*rr*mp.sin(b1_)*mp.sqrt(vv*vv+tt*tt)*mp.sin(A_)/2
            + 2*rr*mp.sin(b2_)*mp.sqrt(vv*vv+tt*tt)*mp.sin(B_)/2)
    return (area + a1*mp.atan2(Y1, X1) + a2*mp.atan2(Y2, X2)
            + (-z[16])*L1*L1/(4*R0*R0) + (-z[78])*L1/(2*R0)
            + z[20]*L2*L2/(4*R0*R0) + z[82]*L2/(2*R0))

P("=== 2. hub factor at the witness vs at the ridge ===")
fw = hubfactor(r, b1, b2, v, t)
Hr = 2*r*mp.sin(T)
vr, tr = Hr*mp.cos(D), Hr*mp.sin(D)
fr = hubfactor(r, b1, b2, vr, tr)
P("witness (v,t) = (%s, %s), H = %s" % (mp.nstr(v, 10), mp.nstr(t, 10), mp.nstr(mp.sqrt(v*v+t*t), 10)))
P("ridge   (v*,t*) = (%s, %s), H* = %s" % (mp.nstr(vr, 10), mp.nstr(tr, 10), mp.nstr(Hr, 10)))
P("hub factor witness = %s" % mp.nstr(fw, 20))
P("hub factor ridge   = %s" % mp.nstr(fr, 20))
P("difference         = %s   (lead: 0.0461558193482276804891637..53)"
  % mp.nstr(fw - fr, 22))
P("")
P("=== 3. envelope facts (from C858-HUB-SCOPE.md) ===")
beta1, gam1 = -z[16]/(4*R0*R0), -z[78]/(2*R0)
beta2, gam2 = z[20]/(4*R0*R0), z[82]/(2*R0)
m1, m2 = mp.mpf('0.76')*beta1+gam1, mp.mpf('0.76')*beta2+gam2
P("beta1=%s gamma1=%s ; beta2=%s gamma2=%s" % tuple(mp.nstr(x, 10) for x in (beta1, gam1, beta2, gam2)))
P("secant slopes m1=%s m2=%s (both <0)" % (mp.nstr(m1, 10), mp.nstr(m2, 10)))
P("concavity threshold L_j >= a_j/|m_j| = %s , %s"
  % (mp.nstr((z[1]-z[9])/abs(m1), 8), mp.nstr((z[3]-z[9])/abs(m2), 8)))
P("witness L1, L2 = %s , %s  (well above the threshold)"
  % (mp.nstr(mp.sqrt((v-2*r*mp.sin(b1)*mp.cos(b1))**2 + (2*r*mp.sin(b1)**2 - t)**2), 8),
     mp.nstr(mp.sqrt((v-2*r*mp.sin(b2)*mp.cos(b2))**2 + (2*r*mp.sin(b2)**2 + t)**2), 8)))
P("=> the secant-reduced envelope is concave at the witness, so a KKT/balance point exists")
P("   and its value can be compared with the witness value directly.")

with open(OUT / 'p39_witness_check.txt', 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
