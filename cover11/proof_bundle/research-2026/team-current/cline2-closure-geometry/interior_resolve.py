"""Clean resolution: for points on the unit circle, the angle at P_k between
P_{k-1} and P_{k+1} must equal pi - (w_{k-1}+w_k)/2.  Test this on the saved
candidate AND on the regular nonagon, with no hand arithmetic."""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]

def angle_at(P, A, B):
    """unsigned angle in [0,pi] between A-P and B-P"""
    u = A-P; v = B-P
    return math.atan2(abs(u[0]*v[1]-u[1]*v[0]), float(u @ v))

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(A[i, 1], A[i, 0]))
c = A[rings+hubs]
S = {}
for k in range(9):
    i, j = k, (k+1) % 9
    m = 0.5*(c[i]+c[j]); d = c[j]-c[i]; n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    for sgn in (+1, -1):
        x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
        if abs(np.linalg.norm(x-c[i])-np.linalg.norm(x-c[j])) > 1e-9: continue
        if np.linalg.norm(x-c[i])-min(np.linalg.norm(q-x) for q in c) > 1e-9: continue
        S[k] = x
th = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
order = sorted(range(9), key=lambda k: th[k])
ths = [th[k] for k in order]
w = {order[m]: (ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)}

print('=== saved candidate ===')
print('arc widths (by switch index):', {k: round(w[k], 6) for k in order})
print(' k | angle(P_{k-1},P_{k+1}) | pi-(w_{k-1}+w_k)/2 | diff')
for k in range(9):
    P = S[k]
    got = angle_at(P, S[(k-1) % 9], S[(k+1) % 9])
    # the two arcs adjacent to P_k are those that end/start at k in the cyclic order
    m = order.index(k)
    wl = (ths[m]-ths[m-1]) % (2*math.pi)
    wr = (ths[(m+1) % 9]-ths[m]) % (2*math.pi)
    pred = math.pi - (wl+wr)/2
    print('%2d | %10.6f | %10.6f | %+.3e' % (k, got, pred, got-pred))

print()
print('=== regular nonagon (arcs 2pi/9) ===')
K = np.array([[math.cos(k*2*math.pi/9), math.sin(k*2*math.pi/9)] for k in range(9)])
for k in range(9):
    got = angle_at(K[k], K[(k-1) % 9], K[(k+1) % 9])
    print('%2d | %.6f | %.6f | diff %.2e' % (k, got, math.pi-2*math.pi/9, got-(math.pi-2*math.pi/9)))
