"""stress-audit debug: exact-rational pivot scan in my elimination order."""
from fractions import Fraction as F
import sys
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global\members\stress-audit\py")
import step5_kernel as K
import json, mpmath as mp
from pathlib import Path

N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
cal = json.loads((N12 / 'evidence/d3-chart-calibration.json').read_text(encoding='utf-8'))
centre = [F(s) for s in cal['root']]
W = K.build_exact([str(c) for c in centre])
Wt = 6 * W['x'] + 6 * W['y'] + 6 * W['z'] + 6 * W['p'] + 3 * W['q'] + 6 * W['u'] + 3 * W['j']
print("weights:", {k: f"{float(v):.8f}" for k, v in W.items() if k in 'xyzpquj'})
print("total W:", f"{float(Wt):.8f}")
L, E = K.laplacian_exact(W, Wt)
print("edges:", len(E))
# per-node weighted degree in the free set
deg = [F(0)] * 27
for i, k, wk in E:
    deg[i] += wk / Wt; deg[k] += wk / Wt
print("free-node degrees:", [f"{float(deg[i]):.5f}" for i in range(18)])

for order_name, order in (("sites,hubs,witnesses", list(range(9)) + list(range(9, 12)) + list(range(12, 18))),
                          ("witnesses,sites,hubs (lead)", list(range(12, 18)) + list(range(0, 12)))):
    M = [[L[i][j] for j in range(27)] for i in range(27)]
    piv = []
    ok = True
    for ii, k in enumerate(order):
        p = M[k][k]; piv.append(p)
        if p <= 0:
            ok = False
            print(f"  [{order_name}] first nonpositive pivot at step {ii}, node {k}: {p}")
            break
        remain = order[ii + 1:] + list(range(18, 27))
        for i in remain:
            if M[i][k] == 0: continue
            for j in remain:
                M[i][j] -= M[i][k] * M[k][j] / p
                if j != i: M[j][i] = M[i][j]
    print(f"  [{order_name}] all pivots > 0: {ok}")
    if ok:
        print("     pivots:", [f"{float(p):.6e}" for p in piv])
        print("     min pivot:", f"{float(min(piv)):.6e}")
