# -*- coding: utf-8 -*-
"""P11: the TRUE tight boundary structure and the switch recursion.

Test 1: is the boundary coverage exactly tight (max_P min_i d(P,c_i) = R) and where?
Test 2: is the own-width w_i equal to the chord bound w_i = 2 asin(min(1,d_i/(2R)))?
Test 3: the recurrences
    (a) t_{i+1} = lam_i + mu_i          (lam_i = t_i - o_i/2, mu_i = t_{i+2} - o_{i+1}/2)
    (b) gamma_{i+1} = t_{i+1} + lam_i + mu_i
"""
import os, sys, math, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
lines = []
def P(s=""):
    lines.append(s); print(s)

with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R = 0.3799838531198387090485181795734298538115979028
ring = [1, 3, 4, 5, 6, 7, 8, 9, 10]
mod = np.linalg.norm(C, axis=1)
psi = np.arctan2(C[:, 1], C[:, 0])
phi = {j: psi[j] for j in ring}
order = sorted(ring, key=lambda j: phi[j])

P("=== TEST 1: boundary coverage tightness ===")
M = 4000001
th = np.linspace(0, 2*np.pi, M, endpoint=False)
Pp = np.stack([np.cos(th), np.sin(th)], axis=1)
Cr = C[ring]
d = np.linalg.norm(Pp[:, None, :]-Cr[None, :, :], axis=2)
mn = d.min(axis=1)
imax = int(np.argmax(mn))
argmaxvals = []
mx = mn.max()
for i in range(M):
    if mn[i] > mx - 1e-15:
        argmaxvals.append(i)
P("max over bd D of min_i d = %.17f   (R = %.17f, diff %+.3e)" % (mx, R, mx-R))
P("argmax angles: %s" % [round(float(th[i]), 12) for i in argmaxvals[:12]])
P("number of argmax samples above mx-1e-15: %d  (grid step %.2e)" % (len(argmaxvals), 2*np.pi/M))
P("closest 2 rings at the argmax:")
ii = argmaxvals[0]
srt = np.argsort(d[ii])
P("   %s" % [(ring[int(k)], "%.12f" % d[ii][k]) for k in srt[:4]])
P("")
P("switches (from P8): args -2.225578224, -1.571880741, -0.918183269, -0.299322048,")
P("                          0.678798368, 1.208634378, 1.930789440, 2.460625451, 2.844... -2.844439442")

def sw_arg(a, b):
    Ca, Cb = C[a], C[b]
    dd = np.linalg.norm(Ca-Cb)
    m = (Ca+Cb)/2
    hh = math.sqrt(max(R*R-dd*dd/4, 0.0))
    perp = np.array([-(Cb-Ca)[1], (Cb-Ca)[0]])/dd
    p1 = m+hh*perp; p2 = m-hh*perp
    p = p1 if np.linalg.norm(p1) <= np.linalg.norm(p2) else p2
    return math.atan2(p[1], p[0]), p

P("")
P("=== TEST 2/3: owned widths, chord bounds, recurrences ===")
sw = {}
for k in range(9):
    a = order[k]; b = order[(k+1) % 9]
    sw[k] = sw_arg(a, b)
t = {j: math.asin(R/mod[j]) for j in ring}
P("%3s %-14s %-14s %-14s %-14s %-14s %-14s" %
  ("k", "ring", "w_k", "2 asin(d_k/2R)", "w-2asin", "2 asin(R/|c|)", "w_i-2t_i"))
W = []
for k in range(9):
    a = order[k]
    w = (sw[k][0]-sw[(k-1) % 9][0]) % (2*math.pi)
    W.append(w)
    dd = np.linalg.norm(C[a]-C[order[(k-1) % 9]])
    P("%3d %-14d %-14.12f %-14.12f %-14.2e %-14.12f %-14.12f" %
      (k, a, w, 2*math.asin(min(1, dd/(2*R))), w-2*math.asin(min(1, dd/(2*R))),
       2*t[a], w-2*t[a]))
P("sum w = %.15f ; 2pi = %.15f" % (sum(W), 2*math.pi))
P("")
P("--- recurrence (a): t_{i+1} = lam_i + mu_i ,  lam_i = t_i - o_i/2, mu_i = t_{i+2} - o_{i+1}/2")
for k in range(9):
    i = order[k]; j = order[(k+1) % 9]; l = order[(k+2) % 9]
    oi = t[i]+t[j]-((psi[j]-psi[i]) % (2*math.pi))
    oj = t[j]+t[l]-((psi[l]-psi[j]) % (2*math.pi))
    lam = t[i]-oi/2; mu = t[l]-oj/2
    P("   k=%d rings(%2d,%2d,%2d): t_j=%.12f  lam+mu=%.12f  diff=%+.2e" %
      (k, i, j, l, t[j], lam+mu, t[j]-(lam+mu)))
P("")
P("--- recurrence (b): gamma_{i+1} = t_{i+1} + lam_i + mu_i")
for k in range(9):
    i = order[k]; j = order[(k+1) % 9]; l = order[(k+2) % 9]
    oi = t[i]+t[j]-((psi[j]-psi[i]) % (2*math.pi))
    oj = t[j]+t[l]-((psi[l]-psi[j]) % (2*math.pi))
    lam = t[i]-oi/2; mu = t[l]-oj/2
    gam = (psi[l]-psi[j]) % (2*math.pi)
    P("   k=%d: gamma=%.12f  t_j+lam+mu=%.12f  diff=%+.2e" % (k, gam, t[j]+lam+mu, gam-(t[j]+lam+mu)))

with open(os.path.join(OUT, "p11_tight_boundary.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines)+"\n")
