"""stress-audit debug 2: compare my Schur complement / pivots with the probe's."""
from fractions import Fraction as F
import sys, json
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global\members\stress-audit\py")
import mpmath as mp
from pathlib import Path

mp.mp.dps = 50
N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
cal = json.loads((N12 / 'evidence/d3-chart-calibration.json').read_text(encoding='utf-8'))
probe = json.loads((N12 / 'evidence/candidate-stress-probe.json').read_text(encoding='utf-8'))
a, t, r, w = [mp.mpf(s) for s in cal['root']]
b = (1 + a + r) / 2
S = b * b + w * w / 3
q = 2 * (1 - b) / r
u = q * r / (2 * a - t + r)
j = u * (2 * t - 2 * r - a) / r
Wt = dict(x=-b * r * r / (S - b), y=(b - 1) * S / (S - b), z=j * r * t / (1 - t * t - r * r),
          p=mp.mpf(1), q=q, u=u, j=j)
tot = 6 * Wt['x'] + 6 * Wt['y'] + 6 * Wt['z'] + 6 * Wt['p'] + 3 * Wt['q'] + 6 * Wt['u'] + 3 * Wt['j']
print("total unnormalised W =", mp.nstr(tot, 20))

E = []
for i in range(9):
    for k in (i, (i + 1) % 9):
        wk = Wt['z'] if k % 3 == 1 else (Wt['x'] if i % 3 == 2 else Wt['y'])
        E.append((18 + i, k, wk))
faces = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]
for fi, f in enumerate(faces):
    for k in f:
        wk = (Wt['q'] if k >= 9 else Wt['p']) if fi < 3 else (Wt['u'] if k >= 9 else Wt['j'])
        E.append((12 + fi, k, wk))
L = mp.zeros(27, 27)
for i, k, wk in E:
    z = wk / tot
    L[i, i] += z; L[k, k] += z; L[i, k] -= z; L[k, i] -= z
print("row sums (abs max):", mp.nstr(max(abs(sum(L[i, jj] for jj in range(27))) for i in range(27)), 6))

# my own Schur complement on anchors
Lff = L[:18, :18]; Lfa = L[:18, 18:]; Laa = L[18:, 18:]
Q = Laa - Lfa.T * (Lff ** -1) * Lfa
print("\nmy Q row0:", [mp.nstr(Q[0, jj], 8) for jj in range(9)])
print("probe Q row0:", [mp.nstr(probe['schur'][0][jj], 8) for jj in range(9)])
print("max |my Q - probe Q| =", mp.nstr(max(abs(Q[i, jj] - probe['schur'][i][jj]) for i in range(9) for jj in range(9)), 6))

# eigenvalues of L_FF
ev = mp.eigsy(Lff, eigvals_only=True)
print("\nsmallest 4 eigenvalues of L_FF:", [mp.nstr(v, 8) for v in ev[:4]])
# pivots in my order (float)
def pivots(order):
    M = mp.matrix(L)
    out = []
    for ii, k in enumerate(order):
        p = M[k, k]; out.append(p)
        if p <= 0:
            return out, False
        remain = order[ii + 1:] + list(range(18, 27))
        for i in remain:
            if M[i, k] == 0: continue
            for jj in remain:
                M[i, jj] -= M[i, k] * M[k, jj] / p
                if jj != i:
                    M[jj, i] = M[i, jj]
    return out, True
for nm, order in (("mine sites,hubs,witness", list(range(9)) + list(range(9, 12)) + list(range(12, 18))),
                  ("lead witnesses,sites,hubs", list(range(12, 18)) + list(range(0, 12)))):
    pv, ok = pivots(order)
    print(f"\n{nm}: all positive {ok}")
    print("  pivots:", [mp.nstr(p, 6) for p in pv])

# is node 17's residual coupling degenerate?  check its neighbours after eliminating sites+hubs
print("\nafter eliminating sites+hubs, conductances from witness17 to witnesses12..16 and anchors")
M = mp.matrix(L)
order = list(range(9)) + list(range(9, 12))
for ii, k in enumerate(order):
    p = M[k, k]
    remain = order[ii + 1:] + list(range(12, 27))
    for i in remain:
        for jj in remain:
            M[i, jj] -= M[i, k] * M[k, jj] / p
            if jj != i: M[jj, i] = M[i, jj]
row = [M[17, jj] for jj in list(range(12, 17)) + list(range(18, 27))]
print("  M[17, .] =", [mp.nstr(x, 6) for x in row])
print("  M[17,17] =", mp.nstr(M[17, 17], 8))
