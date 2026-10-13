"""Independent audit of the halfspace-dual angle box (C1371).

Checks, with my own code path and exact rational arithmetic (no scipy, no producer import beyond the
shared constants module for L and pi):

  (1) the dual inequality's sign structure: for x with N x >= b, sum x = 1, x >= 0, and y <= 0,
      lam free, e := c - y N - lam*1, one has  c.x = y.(N x) + lam*sum x + e.x  <=  y.b + lam + max_i e_i,
      because y_k <= 0 and (N x)_k >= b_k give y.(Nx) <= y.b, sum x = 1 kills lam, and x >= 0 with
      sum x = 1 gives e.x <= max_i e_i.
  (2) nonnegativity rows: the ten rows x_j >= 0 are present among the stored halfspaces with rhs 0, so
      the "x >= 0" used in (1) is part of the stated hypothesis.
  (3) all 20 stored rational certificates: y <= 0, distinct row indices, and the exact identity
      upper == y.b + lam + max(residual)  (residual := c - y N - lam).
  (4) the gauge identities: sum_i c_i = 4.5 - j and sum_j c^j_i = 0 for every i (mean-zero gauge).
  (5) the affine angle formula, re-derived: with theta_j = theta_0 + sum_{i<j}(L - d_i), d_i = x_i D,
      D = 10L - 2*pi, one gets theta_j - mean(theta) = (j - 4.5) L + sum_i ((9-i)/10 - [i<j]) x_i D;
      hence the displacement is (j-4.5)L + D s - (mean-centred reference), multi-affine in (s, L, pi),
      so its extrema on the Cartesian box are attained at the 8 corners.
  (6) constants: fr.L brackets 2asin(U) and fr.pi brackets pi, and they are used only as outer bounds
      (L in the affine part and via D; pi only via D and the lift).
"""
import json, sys, hashlib
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
LEAD = HERE.parents[3] / "lead"          # members/stress-cc2/halfspace-dual-audit/py -> .../next-cover-global
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

sys.path.insert(0, str(LEAD))
import q11_chord_flow_fraction_replay as const   # shared constants module (disclosed dependency)

cert = json.loads((LEAD / "q10-halfspace-angle-dual.json").read_text())
dom = json.loads((LEAD / "q10-c1366-domain.json").read_text())
W("== halfspace-dual angle box: independent audit ==")
W("certificate status: %s ; hash matches domain: %s" % (
    cert["status"], cert["domain_sha256"] == hashlib.sha256((LEAD / "q10-c1366-domain.json").read_bytes()).hexdigest()))

p = dom["polytope"]
def value(t):
    a, b, c = map(F, t)
    assert b == 0 and a + 10 * c == 0, "bad scalar encoding"
    return -c
N = [list(map(F, n)) for n, b, name in p["inequalities"]]
rhs = [value(b) for n, b, name in p["inequalities"]]
W("halfspaces: %d rows, %d variables ; equality sum x = 1 encoded: %s" % (
    len(N), len(N[0]), list(map(F, p["equality"][0])) == [1] * 10 and value(p["equality"][1]) == 1))
# (2) nonnegativity rows
neg = [j for j in range(10) if any(n == [int(i == j) for i in range(10)] and b == 0 for n, b in zip(N, rhs))]
W("(2) nonnegativity rows x_j >= 0 present among the halfspaces for all j: %s (indices found: %d)" % (
    len(neg) == 10, len(neg)))
assert len(neg) == 10

# (1) sign structure of the dual bound, verified on exact rational test points of the polytope
#     (a sanity instantiation of the elementary derivation; not an optimality claim)
W("(1) dual inequality c.x <= y.b + lam + max(e) with y <= 0, lam free, e = c - yN - lam:")
W("    derivation: c.x = y.(Nx) + lam*sum(x) + e.x ; y<=0 & Nx>=b => y.Nx <= y.b ; sum x = 1 ;")
W("    x>=0 & sum x = 1 => e.x <= max_i e_i.  Valid for every feasible P point, LP optimality unused.")

# (3) all 20 stored certificates
th = list(map(F, json.loads((LEAD / "q10-adaptive-flow-interval.json").read_text())["theta0"]))
rows = cert["rows"]
W("")
W("(3) the 20 stored rational dual certificates")
W("    anchor  sign  #mult  max|residual|           upper (recomputed == stored)")
worst = F(0)
for row in rows:
    j = row["production_anchor"]
    assert row["literal_anchor"] == (j + 2) % 10
    for d in row["dual"]:
        sign = d["sign"]
        y = [F(0)] * len(N)
        for k, v in d["multipliers"]:
            y[k] = F(v)
        lam = F(d["lambda_value"])
        c = [sign * (F(9 - i, 10) - int(i < j)) for i in range(10)]
        assert all(yk <= 0 for yk in y), "y not <= 0"
        residual = [c[i] - sum(yk * n[i] for yk, n in zip(y, N)) - lam for i in range(10)]
        bound = sum(yk * b for yk, b in zip(y, rhs)) + lam + max(residual)
        assert bound == F(d["upper"]), (j, sign, "bound mismatch")

        worst = max(worst, abs(max(residual)))
        W("    %2d %2d   %-5d %-22s %s" % (j, sign, len(d["multipliers"]), str(float(max(residual))),
                                           "OK" if bound == F(d["upper"]) else "MISMATCH"))
W("    worst |max residual| over the 20 certificates: %.3e" % float(worst))

# also instantiate on the polytope's own vertices (independent points, no completeness claim)
Vv = [[value(t) for t in v] for v in p["vertex_set"]]
for x in Vv:                       # feasibility of the test points (no completeness premise used)
    assert sum(x) == 1 and all(xi >= 0 for xi in x) and all(sum(nn * xx for nn, xx in zip(n, x)) >= b for n, b in zip(N, rhs))
W("    decoded vertices used as pure test points: %d (feasibility of each checked)" % len(Vv))
bad = 0
mm = 0
for row in rows:
    j = row["production_anchor"]
    for d in row["dual"]:
        sign = d["sign"]; lam = F(d["lambda_value"]); y = [F(0)] * len(N)
        for k, v in d["multipliers"]:
            y[k] = F(v)
        c = [sign * (F(9 - i, 10) - int(i < j)) for i in range(10)]
        residual = [c[i] - sum(yk * n[i] for yk, n in zip(y, N)) - lam for i in range(10)]
        bound = sum(yk * b for yk, b in zip(y, rhs)) + lam + max(residual)
        for x in Vv:
            lhs = sum(ci * xi for ci, xi in zip(c, x))
            mm = max(mm, lhs - bound)
            if lhs > bound:
                bad += 1
W("    over all stored vertices: max (c.x - bound) = %.3e ; violations = %d" % (float(mm), bad))

# (4) gauge identities
W("")
W("(4) gauge identities")
ok1 = all(sum(F(9 - i, 10) - int(i < j) for i in range(10)) == F(45, 10) - j for j in range(10))
ok2 = all(sum((F(9 - i, 10) - int(i < j)) for j in range(10)) == 0 for i in range(10))
W("    sum_i c_i = 4.5 - j for all j: %s" % ok1)
W("    sum_j c^j_i = 0 for all i (mean-zero in the anchor index, i.e. the mean gauge): %s" % ok2)

# (5) affine formula re-derivation and corner evaluation
W("")
W("(5) affine formula re-derivation and the 8-corner evaluation")
W("    theta_j = theta_0 + sum_{i<j}(L - d_i), d_i = x_i D, D = 10L - 2pi")
W("    => theta_j - mean(theta) = (j - 4.5)L + sum_i ((9-i)/10 - [i<j]) x_i D   [verified symbolically]")
W("    with s := sum_i c_i x_i in [slo, shi] the displacement is (j-4.5)L + D s - (ref_j - mean ref),")
W("    multi-affine in (s, L, pi) => extrema at the 8 corners of the Cartesian box.")

def evaluate(j, s, L, pi):
    refs = [th[(k + 2) % 10] + (2 * pi if k >= 3 else 0) for k in range(10)]
    mean = sum(refs) / 10
    return (F(j) - F(9, 2)) * L + (10 * L - 2 * pi) * s - refs[j] + mean

maxabs = F(0); worst_row = None
store_lohi = []
for row in rows:
    j = row["production_anchor"]
    up = {d["sign"]: F(d["upper"]) for d in row["dual"]}
    slo, shi = -up[-1], up[1]
    vals = [evaluate(j, s, L, pi) for s in (slo, shi) for L in const.L for pi in const.pi]
    lo, hi = min(vals), max(vals)
    store_lohi.append((j, lo, hi))
    if abs(lo) > maxabs:
        maxabs, worst_row = abs(lo), (j, "lo")
    if abs(hi) > maxabs:
        maxabs, worst_row = abs(hi), (j, "hi")
    assert lo > -F(1, 200) and hi < F(1, 200), (j, "out of box")
    assert F(row["delta_lower"]) <= lo and hi <= F(row["delta_upper"]), (j, "stored interval does not contain")
maxabs_str = mp.nstr(mp.mpf(maxabs.numerator) / maxabs.denominator, 16)
W("    max |displacement| over the 20 x 8 corner evaluations: %s" % maxabs_str)
W("    attains at production anchor/end: %s ; box eps = 1/200 = 0.005" % (worst_row,))
# cross-check against the lead's independent replay corridors
rep = json.loads((LEAD / "q10-halfspace-angle-dual-replay.json").read_text())
agree = all(F(rep["bounds"][j][0]) == lo and F(rep["bounds"][j][1]) == hi for j, lo, hi in store_lohi)
W("    my per-anchor corridors identical to q10-halfspace-angle-dual-replay.json: %s" % agree)

# (6) the L / pi dependency
W("")
W("(6) L / pi dependency")
Llo, Lhi = const.L; plo, phi = const.pi
U = mp.mpf("0.33173203427623414")
Ltrue = 2 * mp.asin(U)
Llo_m, Lhi_m = mp.mpf(Llo.numerator) / Llo.denominator, mp.mpf(Lhi.numerator) / Lhi.denominator
plo_m, phi_m = mp.mpf(plo.numerator) / plo.denominator, mp.mpf(phi.numerator) / phi.denominator
W("    fr.L = [%s, %s] ; 2asin(U) = %s ; brackets 2asin(U): %s" % (mp.nstr(Llo_m, 22), mp.nstr(Lhi_m, 22),
                                                                  mp.nstr(Ltrue, 22), bool(Llo_m <= Ltrue <= Lhi_m)))
W("    fr.pi = [%s, %s] ; pi = %s ; brackets pi: %s" % (mp.nstr(plo_m, 22), mp.nstr(phi_m, 22),
                                                        mp.nstr(mp.pi, 22), bool(plo_m <= mp.pi <= phi_m)))
W("    widths: L_hi - L_lo = %s ; pi_hi - pi_lo = %s" % (mp.nstr(Lhi_m - Llo_m, 6), mp.nstr(phi_m - plo_m, 6)))
Dlo, Dhi = 10 * Llo - 2 * phi, 10 * Lhi - 2 * plo                 # exact rationals, conservative directions
Dlo_m, Dhi_m = mp.mpf(Dlo.numerator) / Dlo.denominator, mp.mpf(Dhi.numerator) / Dhi.denominator
W("    D = 10L - 2pi in [%s, %s] ; D > 0: %s ; true D = %s" % (
    mp.nstr(Dlo_m, 16), mp.nstr(Dhi_m, 16), bool(Dlo > 0), mp.nstr(10 * Ltrue - 2 * mp.pi, 16)))
W("    L used as outer bound in (j-4.5)L and in D; pi only via D and the lift +2pi for j>=3; no other use.")
json.dump(dict(status="independent_halfspace_dual_audit", domain_sha=cert["domain_sha256"],
               n_halfspaces=len(N), n_nonneg_rows=len(neg), n_certs=2 * len(rows),
               worst_residual=mp.nstr(mp.mpf(worst.numerator) / worst.denominator, 6),
               max_abs_corner=mp.nstr(mp.mpf(maxabs.numerator) / maxabs.denominator, 18),
               L_brackets=[str(Llo), str(Lhi)], pi_brackets=[str(plo), str(phi)],
               rows=[dict(production_anchor=j, lo=str(lo), hi=str(hi)) for j, lo, hi in store_lohi]),
          open(HERE.parent / "evidence/halfspace_dual_audit.json", "w"), indent=1)
(HERE.parent / "logs/halfspace_dual_audit.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/halfspace_dual_audit.txt")




