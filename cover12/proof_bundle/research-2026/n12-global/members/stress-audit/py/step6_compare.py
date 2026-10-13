"""stress-audit step 6: interface cross-checks (classification / normalisation / grid).

  C1  probe nullspace weights (36, its own LU)  vs  7-orbit weights/W
  C2  lead stress-interval.json Dirichlet pivots (their order) vs my kernel, same box
  C3  lead exact_cosine_constants vs my Chebyshev T_d(1-2U^2)
  C4  lead weight_bounds / normalization vs my interval kernel on their box
"""
from fractions import Fraction as F
from pathlib import Path
import json, sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.set_int_max_str_digits(10**6)
import step5_kernel as K

N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
probe = json.loads((N12 / 'evidence/candidate-stress-probe.json').read_text(encoding='utf-8'))
siv = json.loads((N12 / 'evidence/stress-interval.json').read_text(encoding='utf-8'))
cal = json.loads((N12 / 'evidence/d3-chart-calibration.json').read_text(encoding='utf-8'))
U = F('0.361102963744508672616920293904')
out = {}
box = siv['box']

print("=== C1. probe 36 nullspace weights vs 7-orbit normalised weights ===")
W = K.build(box)
Wt = K.total(W)
orb = K.weights_of(W)
plan = []
for i in range(9):
    for k in (i, (i + 1) % 9):
        plan.append('z' if k % 3 == 1 else ('x' if i % 3 == 2 else 'y'))
faces = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]
for fi, f in enumerate(faces):
    for k in f:
        plan.append(('q' if k >= 9 else 'p') if fi < 3 else ('u' if k >= 9 else 'j'))
assert len(plan) == 36
rows, worst = [], (0.0, None)
for idx, (pw, let) in enumerate(zip(probe['weights'], plan)):
    lo = float(orb[let].lo / Wt.hi); hi = float(orb[let].hi / Wt.lo)
    mid = 0.5 * (lo + hi)
    rel = abs(pw - mid) / max(abs(pw), 1e-300)
    if rel > worst[0]:
        worst = (rel, idx)
    rows.append({'edge': probe['edges'][idx], 'orbit': let, 'probe_weight': pw,
                 'my_bracket': [lo, hi], 'rel_dev': rel})
print(f"  max relative deviation over all 36 weights: {worst[0]:.3e} at {probe['edges'][worst[1]]}")
print(f"  probe weight sum = {sum(probe['weights']):.15f};  my W bracket = [{float(Wt.lo):.9f}, {float(Wt.hi):.9f}]")
out['C1'] = {'max_rel_dev': worst[0], 'argmax': list(probe['edges'][worst[1]]),
             'probe_weight_sum': sum(probe['weights']), 'rows': rows}

print("\n=== C2. my kernel in the LEAD's order vs their recorded pivots ===")
W2 = K.build(box, 10**45)
Wt2 = K.total(W2)
L2 = K.laplacian(K.edges_of(W2), Wt2)
lead_order = list(range(12, 18)) + list(range(0, 12))
Q2, piv2 = K.schur(L2, lead_order)
rec = [F(s[0]) for s in siv['dirichlet_pivots']]
rec_hi = [F(s[1]) for s in siv['dirichlet_pivots']]
print("  #mine =", len(piv2), " #recorded =", len(rec))
devs = []
for i, (a, b, bh) in enumerate(zip(piv2, rec, rec_hi)):
    dv = max(abs(a.lo - b), abs(a.hi - bh))
    rel = float(dv) / float(abs(b))
    devs.append(rel)
    if i < 6 or i >= 15:
        print(f"  pivot {i:2d}: mine [{float(a.lo):.12e},{float(a.hi):.12e}]  recorded [{float(b):.12e},{float(bh):.12e}]  rel {rel:.2e}")
print(f"  max relative deviation of recorded pivots vs my interval: {max(devs):.3e}")
out['C2'] = {'max_rel_dev': max(devs), 'n': len(piv2),
             'mine_float': [f"{(float(a.lo)+float(a.hi))/2:.12e}" for a in piv2],
             'recorded_float': [f"{float(b):.12e}" for b in rec]}

print("\n=== C3. exact cosine constants ===")
cosd = K.cos_table(U)
rec_cos = [F(s) for s in siv['exact_cosine_constants']]
mine = [F(1)] + [cosd[d] for d in (1, 2, 3, 4)]
same = all(a == b for a, b in zip(rec_cos, mine))
print("  recorded == my Chebyshev T_d(1-2U^2):", same)
for d, (a, b) in enumerate(zip(rec_cos, mine)):
    print(f"    d={d}: recorded {float(a):.15f}  mine {float(b):.15f}  equal {a == b}")
out['C3'] = {'identical': same,
             'cos_float': {str(d): f"{float(v):.15f}" for d, v in cosd.items()},
             'recorded_float': [f"{float(v):.15f}" for v in rec_cos]}

print("\n=== C4. weight bounds and normalisation ===")
mine_w = {k: v.dump() for k, v in orb.items()}
rec_w = siv['weight_bounds']
for k in ('x', 'y', 'z', 'p', 'q', 'u', 'j'):
    a = [F(s) for s in mine_w[k]]; b = [F(s) for s in rec_w[k]]
    print(f"  {k}: mine [{float(a[0]):.12e},{float(a[1]):.12e}]  recorded [{float(b[0]):.12e},{float(b[1]):.12e}]"
          f"  |diff|<= {float(max(abs(a[0]-b[0]), abs(a[1]-b[1]))):.2e}")
rn = [F(s) for s in siv['normalization']]
print(f"  normalisation: mine [{float(Wt2.lo):.12e},{float(Wt2.hi):.12e}]  recorded [{float(rn[0]):.12e},{float(rn[1]):.12e}]")
print(f"  min Schur conductance: mine {float(min(-Q2[i][j].hi for i in range(9) for j in range(i+1,9))):.6e}"
      f"  recorded {float(F(siv['minimum_schur_conductance_lower'])):.6e}")
out['C4'] = {'min_conductance_mine_float': float(min(-Q2[i][j].hi for i in range(9) for j in range(i + 1, 9))),
             'min_conductance_recorded_float': float(F(siv['minimum_schur_conductance_lower'])),
             'normalisation_mine': [float(Wt2.lo), float(Wt2.hi)],
             'normalisation_recorded': [float(rn[0]), float(rn[1])]}

p = N12 / 'members/stress-audit/evidence/stress-audit-crosscheck.json'
p.write_text(json.dumps(out, indent=1), encoding='utf-8')
print("\nwrote", p)
