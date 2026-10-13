# -*- coding: utf-8 -*-
"""P1 (v2): inward-root fan geometry of the saved certified object.

COLUMN SEMANTICS (caliber, fixed):
  b_j  = |c_j|                    (centre modulus, units of unit-disk radius)
  r_j  = 1 - |c_j|                (distance from centre to bd D)  [NOT the same as b_j]
  t_j  = asin(R/b_j) when b_j>=R  (arc half-width on bd D, radians)
  a*   = min_j (|c_j| - R) over rings  = slack of the ring system to bd D
  a    = 1 - 2R  (core radius; the two hubs must cover closed B(0,a))

  ring  j : |c_j| + R >= 1  (its disk meets bd D; |c_j| >= 1-R)
  hub   j : |c_j| + R <  1  (strictly interior; covers no point of bd D)
"""
import os, sys
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import load_object, classify, HERE

mp.mp.dps = 60
OUT = os.path.join(HERE, os.pardir, "out")
os.makedirs(OUT, exist_ok=True)
lines = []
def P(s=""):
    lines.append(s); print(s)

C, R, mp = load_object()
ring, hub, mod = classify(C, R)
P("#" * 78)
P("R = %s   (interval midpoint of certified_object.json)" % mp.nstr(R, 48))
P("ring sites %s" % ring)
P("hub  sites %s" % hub)
P("#" * 78)
P("")
P("%3s %-24s %-22s %-22s %-24s" % ("j", "b_j=|c_j|", "r_j=1-|c_j|", "b_j+R-1", "t_j=asin(R/b_j)"))
info = {}
for j in range(11):
    b = mod[j]
    t = mp.asin(R/b) if b >= R else mp.mpf(0)
    phi = mp.atan2(C[j][1], C[j][0])
    info[j] = dict(b=b, r=1-b, t=t, phi=phi)
    P("%3d %-24s %-22s %-22s %-24s  phi=%s" %
      (j, mp.nstr(b, 18), mp.nstr(1-b, 18), mp.nstr(b+R-1, 18), mp.nstr(t, 18),
       mp.nstr(phi, 18)))
a_star = min(info[j]['b'] for j in ring) - R
P("")
P("a* = min_ring (b_j - R) = %s" % mp.nstr(a_star, 20))
P("min_tip_x - R where tip_x is the deepest hub-only point ... (see p2)")
P("")
P("sum_j t_j (rings) = %s ; pi = %s ; diff = %s"
  % (mp.nstr(sum(info[j]['t'] for j in ring), 25), mp.nstr(mp.pi, 25),
     mp.nstr(sum(info[j]['t'] for j in ring) - mp.pi, 12)))
P("2*sum_j t_j       = %s ; 2pi = %s ; diff = %s"
  % (mp.nstr(2*sum(info[j]['t'] for j in ring), 25), mp.nstr(2*mp.pi, 25),
     mp.nstr(2*sum(info[j]['t'] for j in ring) - 2*mp.pi, 12)))

order = sorted(ring, key=lambda j: info[j]['phi'])
P("")
P("cyclic ring order (increasing polar angle): %s" % order)
P("")
P("arc-overlap ledger (arc_i = [phi_i - t_i, phi_i + t_i]):")
P("%-14s %-16s %-16s %-16s %-16s" % ("pair", "gamma", "t_i+t_j", "overlap o", "t_i+t_j-gamma"))
for k in range(9):
    i = order[k]; jj = order[(k+1) % 9]
    g = (info[jj]['phi'] - info[i]['phi']) % (2*mp.pi)
    P("%-14s %-16s %-16s %-16s %-16s" %
      ("(%d,%d)" % (i, jj), mp.nstr(g, 16), mp.nstr(info[i]['t']+info[jj]['t'], 16),
       mp.nstr(info[i]['t']+info[jj]['t']-g, 16), mp.nstr(info[i]['t']+info[jj]['t']-g, 16)))

def switch_inner(i, jj):
    """inner crossing on bd D of bd B(c_i,R) and bd B(c_jj,R) (the one with |P|<1 side)."""
    a = C[i]; b = C[jj]
    d = mp.sqrt((a[0]-b[0])**2 + (a[1]-b[1])**2)
    m = ((a[0]+b[0])/2, (a[1]+b[1])/2)
    h2 = R*R - d*d/4
    hh = mp.sqrt(max(h2, mp.mpf(0)))
    perp = (-(b[1]-a[1])/d, (b[0]-a[0])/d)
    p1 = (m[0] + hh*perp[0], m[1] + hh*perp[1])
    p2 = (m[0] - hh*perp[0], m[1] - hh*perp[1])
    n1 = mp.sqrt(p1[0]**2 + p1[1]**2); n2 = mp.sqrt(p2[0]**2 + p2[1]**2)
    return p1 if n1 <= n2 else p2

P("")
P("switches P_k between ring-order k and k+1:")
sw = {}
for k in range(9):
    i = order[k]; jj = order[(k+1) % 9]
    p = switch_inner(i, jj)
    sw[k] = p
    P("   P_%d (%2d,%2d) |P|=%s arg=%s  resid to ring i=%s  to ring j=%s"
      % (k, i, jj, mp.nstr(mp.sqrt(p[0]**2+p[1]**2), 24),
         mp.nstr(mp.atan2(p[1], p[0]), 18),
         mp.nstr(mp.sqrt((p[0]-C[i][0])**2+(p[1]-C[i][1])**2) - R, 4),
         mp.nstr(mp.sqrt((p[0]-C[jj][0])**2+(p[1]-C[jj][1])**2) - R, 4)))
P("")
P("owned arc widths w_k (position k owns P_{k-1} -> P_k):")
W = []
for k in range(9):
    pm = sw[(k-1) % 9]; pp = sw[k]
    w = (mp.atan2(pp[1], pp[0]) - mp.atan2(pm[1], pm[0])) % (2*mp.pi)
    W.append(w)
    P("   w_%d = %-22s  site %2d  (2t=%s, overlap w-2t=%s)"
      % (k, mp.nstr(w, 20), order[k], mp.nstr(2*info[order[k]]['t'], 18),
         mp.nstr(w-2*info[order[k]]['t'], 8)))
P("   sum w = %s vs 2pi = %s  diff = %s"
  % (mp.nstr(sum(W), 25), mp.nstr(2*mp.pi, 25), mp.nstr(sum(W)-2*mp.pi, 8)))

# chain structure: blocks of consecutive rings feeding one hub
a_core = 1 - 2*R
P("")
P("core radius a = 1-2R = %s ; R-a = %s ; sqrt(R^2-a^2) = %s"
  % (mp.nstr(a_core, 18), mp.nstr(R-a_core, 18), mp.nstr(mp.sqrt(R*R-a_core**2), 18)))
for j in hub:
    s = info[j]['b']
    val = (a_core*a_core + s*s - R*R)/(2*a_core*s)
    P("   hub %d: |h|=%s ; cos(b_j)=%s ; b_j = %s ; delta_j = pi-b_j = %s"
      % (j, mp.nstr(s, 18), mp.nstr(val, 18),
         mp.nstr(mp.acos(max(mp.mpf(-1), min(mp.mpf(1), val))), 18),
         mp.nstr(mp.pi - mp.acos(max(mp.mpf(-1), min(mp.mpf(1), val))), 18)))
h0, h1 = hub
dhh = mp.sqrt((C[h0][0]-C[h1][0])**2 + (C[h0][1]-C[h1][1])**2)
delta = mp.acos((C[h0][0]*C[h1][0]+C[h0][1]*C[h1][1])/(info[h0]['b']*info[h1]['b']))
P("   hub-hub distance = %s ; delta(h0,h1) = %s ; pi-delta = %s"
  % (mp.nstr(dhh, 18), mp.nstr(delta, 20), mp.nstr(mp.pi-delta, 20)))
P("   hub separation in units of 2R: d/(2R) = %s" % mp.nstr(dhh/(2*R), 18))

# chain half-angle L_i and offset Delta_i for the arc owned by ring i
P("")
P("chain half-angles (inward-root fan): rho_i, L_i, Delta_i = t_i + 2 L_i")
P("%3s %-22s %-22s %-22s %-22s" % ("j", "rho_j=|c_j|", "L_j", "Delta_j", "pi-Delta_j"))
rr = {}
LL = {}
DD = {}
for j in ring:
    rho = info[j]['b']; t = info[j]['t']
    L = mp.atan2(mp.sin(t), rho - mp.cos(t))
    rr[j] = rho; LL[j] = L; DD[j] = t + 2*L
    P("%3d %-22s %-22s %-22s %-22s" % (j, mp.nstr(rho, 18), mp.nstr(L, 18),
                                       mp.nstr(t+2*L, 18), mp.nstr(mp.pi - t - 2*L, 18)))
P("")
P("check: phi_k - Delta_k (increasing) vs switch args  [P_{k-1} should equal phi_k - Delta_k]")
srt = sorted(ring, key=lambda j: info[j]['phi'] - DD[j])
for j in srt:
    P("   site %2d : phi-Delta = %s   phi+Delta = %s"
      % (j, mp.nstr(info[j]['phi']-DD[j], 18), mp.nstr(info[j]['phi']+DD[j], 18)))
P("   switch args: %s" % [mp.nstr(mp.atan2(sw[k][1], sw[k][0]), 18) for k in range(9)])

with open(os.path.join(OUT, "p1_geometry.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
