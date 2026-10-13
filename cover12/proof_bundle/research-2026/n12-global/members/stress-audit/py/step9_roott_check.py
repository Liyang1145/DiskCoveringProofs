"""stress-audit step 9: independent interval re-verification of the root-T certificate
using MY interval primitive (different rounding grid/implementation) and of the
same-box stress inequalities.

  R1  parse F,G,H,T and the certified box from evidence/root-t-certificate.json
  R2  ||I - Y J(box)||_inf < 1 and Krawczyk image K strictly inside the box
  R3  weights/pivots/M-positive on THAT exact box (my kernel)
"""
from fractions import Fraction as F
from pathlib import Path
import json, sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.set_int_max_str_digits(10**6)
import sympy as sp
import step5_kernel as K

N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
cert = json.loads((N12 / 'evidence/root-t-certificate.json').read_text(encoding='utf-8'))
print("status:", cert['status'])
print("proposition:", cert['proposition'])
print("recorded contraction norm:", cert['contraction_norm_upper'])
print("recorded selfmap margins:", cert['selfmap_margins'])

a, t, r, w = sp.symbols('a t r w')
xs = (a, t, r, w)
polys = [sp.sympify(s) for s in cert['polynomials']]
box = [(F(s[0]), F(s[1])) for s in cert['box']]
Yr = [[F(v) for v in row] for row in cert['preconditioner']]
centre = [(lo + hi) / 2 for lo, hi in box]
rad = [max(c - lo, hi - c) for c, (lo, hi) in zip(centre, box)]
print("\nbox:", [(float(lo), float(hi)) for lo, hi in box])
print("radii:", [float(x) for x in rad])

# ---- R1/R2 with my own interval primitive -----------------------------------
K.IV.SCALE = 10**60
box_iv = [K.IV(lo, hi) for lo, hi in box]
J = sp.Matrix(polys).jacobian(xs)

def ev_iv(poly):
    """interval evaluation of a polynomial with integer coefficients."""
    P = sp.Poly(sp.expand(poly), *xs)
    acc = K.IV(0)
    for mon, c in zip(P.monoms(), P.coeffs()):
        term = K.IV(F(int(c.p), int(c.q)))
        for x, n in zip(box_iv, mon):
            term = term * x ** n
        acc = acc + term
    return acc

def ev_exact(poly, pt):
    P = sp.Poly(sp.expand(poly), *xs)
    acc = F(0)
    for mon, c in zip(P.monoms(), P.coeffs()):
        term = F(int(c.p), int(c.q))
        for x, n in zip(pt, mon):
            term *= x ** n
        acc += term
    return acc

fc = [ev_exact(poly, centre) for poly in polys]
print("\nexact residuals at the box centre:", [float(v) for v in fc])
JI = [[ev_iv(J[i, j]) for j in range(4)] for i in range(4)]
B = [[K.IV(int(i == j)) - sum((K.IV(Yr[i][k]) * JI[k][j] for k in range(4)), K.IV(0)) for j in range(4)]
     for i in range(4)]
q = max(sum(max(abs(x.lo), abs(x.hi)) for x in row) for row in B)
print("my ||I - Y J(box)||_inf upper bound =", f"{float(q):.6e}", " <1:", q < 1)
Ki = []
for i in range(4):
    val = K.IV(centre[i]) - sum((K.IV(Yr[i][k]) * K.IV(fc[k]) for k in range(4)), K.IV(0)) \
          + sum((B[i][j] * K.IV(-rad[j], rad[j]) for j in range(4)), K.IV(0))
    Ki.append(val)
inside = all(lo < val.lo and val.hi < hi for val, (lo, hi) in zip(Ki, box))
print("Krawczyk image inside box (my intervals):", inside)
for i, val in enumerate(Ki):
    print(f"   x{i}: K=[{float(val.lo):.12e},{float(val.hi):.12e}]  margins "
          f"{float(min(val.lo-box[i][0], box[i][1]-val.hi)):.3e}")

# ---- R3 stress inequalities on THAT box, my kernel --------------------------
print("\n=== R3: stress kernel on the certified root box (my order) ===")
order = list(range(9)) + list(range(9, 12)) + list(range(12, 18))
for grid in (10**60, 10**45, 10**30):
    Wd = K.build([[str(lo), str(hi)] for lo, hi in box], grid)
    wt = K.weights_of(Wd)
    Wt = K.total(Wd)
    L = K.laplacian(K.edges_of(Wd), Wt)
    Q, piv = K.schur(L, order)
    cosd = K.cos_table(F('0.361102963744508672616920293904'))
    M, qmin = K.M_matrix(Q, cosd)
    G = K.gram_1perp(M)
    gpiv = K.ldl(G, 8)
    print(f"  grid 1e{len(str(grid))-1}: weights>0 {all(v.lo>0 for v in wt.values())}  W>0 {Wt.lo>0}  "
          f"min pivot {float(min(p.lo for p in piv)):.4e}  min q {float(qmin):.4e}  "
          f"min Gram pivot {float(min(p.lo for p in gpiv)):.4e}")

out = {'q_upper': f"{float(q):.6e}", 'q_lt_1': bool(q < 1), 'krawczyk_inside': bool(inside),
       'selfmap_margins_mine': [f"{float(min(val.lo-box[i][0], box[i][1]-val.hi)):.6e}" for i, val in enumerate(Ki)],
       'centre_residuals': [f"{float(v):.3e}" for v in fc], 'grid_used': '10^-60'}
(N12 / 'members/stress-audit/evidence/stress-audit-roottcheck.json').write_text(json.dumps(out, indent=1), encoding='utf-8')
print("\nwrote evidence/stress-audit-roottcheck.json")
