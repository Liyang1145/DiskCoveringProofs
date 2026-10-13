import numpy as np
r = 0.38
C = np.array([[ 0.858810938, 0.000000000],   # placeholder, replaced below
              ])
# certified object ring centres (9 of them)
rings = np.array([
 [ 0.858810938, 0.000000000],
])
# build from raw integers
rings = np.array([
 [-0.00016204298677169, 0.89252120511936428][::1],
])
# simpler: hard-code from file
import io, json
d = json.load(io.open('n11/upper/certified_object.json', encoding='utf-8'))
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in d['centers_scaled_1e17']])
rho = np.hypot(C[:, 0], C[:, 1])
R9 = C[rho >= 0.62]
H2 = C[rho < 0.62]
print("9 ring centres:"); 
for c in R9: print("   (%+.9f, %+.9f) |c|=%.9f" % (c[0], c[1], np.hypot(*c)))
print("2 hubs:"); 
for c in H2: print("   (%+.9f, %+.9f) |c|=%.9f" % (c[0], c[1], np.hypot(*c)))

def mind(p, S):   # min distance from p to set S
    return np.sqrt(((np.asarray(p) - S)**2).sum(-1).min())

print("\n-- is the hole nonempty? sample the ring-only covering radius over D --")
th = np.linspace(0, 2*np.pi, 3000, endpoint=False)
U = np.stack([np.cos(th), np.sin(th)], 1)
best = -1; bp = None
for d_ in np.linspace(0, 1, 700):
    P = d_*U
    v = np.sqrt(((P[:, None, :] - R9[None, :, :])**2).sum(-1).min(1))
    k = int(np.argmax(v))
    if v[k] > best: best = float(v[k]); bp = P[k].copy()
print("   max_{x in D} min_{ring} |x-a| = %.8f  (r=%.4f)  at %s |.|=%.6f" % (best, r, np.round(bp,6), np.hypot(*bp)))
print("   ring-only covering radius exceeds r -> hole nonempty:", best > r)

print("\n-- min distance to the 2 hubs at that point --")
print("   dist to hubs:", np.round(np.sqrt(((bp - H2)**2).sum(-1)), 8))
print("\n-- how much of D do the 9 rings cover? --")
P = np.stack([np.cos(np.linspace(0,2*np.pi,3000,endpoint=False)), np.sin(np.linspace(0,2*np.pi,3000,endpoint=False))],1)
for d_ in (0.1, 0.2, 0.24, 0.32, 0.4, 0.5, 0.6, 0.62, 0.7, 0.8, 0.9, 1.0):
    Q = d_*P
    v = np.sqrt(((Q[:, None, :] - R9[None, :, :])**2).sum(-1).min(1))
    print("   |x|=%.2f : min %.4f  max %.4f  fraction outside rings %.3f" % (d_, v.min(), v.max(), (v > r).mean()))
