import numpy as np, io, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

d = json.load(io.open('n11/upper/certified_object.json', encoding='utf-8'))
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in d['centers_scaled_1e17']])

def rho_of(C):
    return np.hypot(C[:, 0], C[:, 1])

print("|c_i| =", np.round(rho_of(C), 8))

# Dense evaluation of r(c) = max_{x in D} min_i |x-c_i|
def grid_max(C, nth=1440, nd=800):
    best = -1; bp = None
    th = np.linspace(0, 2*np.pi, nth, endpoint=False)
    ds = np.linspace(0, 1, nd)
    U = np.stack([np.cos(th), np.sin(th)], 1)   # nth x 2
    for d_ in ds:
        P = d_*U
        D2 = ((P[:, None, :] - C[None, :, :])**2).sum(-1)
        v = np.sqrt(D2.min(1))
        k = int(np.argmax(v))
        if v[k] > best:
            best = float(v[k]); bp = P[k].copy()
    return best, bp

b, bp = grid_max(C)
print("dense grid max_{x in D} min_i |x-c_i| =", b, "at", np.round(bp, 6), " |bp|=", np.hypot(*bp))
