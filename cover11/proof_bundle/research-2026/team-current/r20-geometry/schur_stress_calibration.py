"""r20-geometry Round-16 (lead fd64d79e): CALIBRATION of the corrected Schur-energy interface.

Correct object (lead):  E_alpha(U) = MIN over free nodes of  sum_e alpha_e |edge_e|^2  at fixed anchors U.
Lagrangian route (lead): L = t + sum_e alpha_e (|edge_e|^2 - t);
  inf over t forces sum_e alpha_e = 1;  inf over the free nodes gives E_alpha(U);
  Slater => V(U)^2 = max_{alpha in simplex} E_alpha(U) with E_alpha CONCAVE (generally NONLINEAR) in alpha.

This script calibrates exactly (sympy + exact rationals), no downstream work:
  K1  single-edge simplex vertex: one edge, one free endpoint X, one anchor U -> E = min_X |U-X|^2 = 0
  K2  two-edge path, weights (a, 1-a):  E_a(U) = min_X (a|U-X|^2 + (1-a)|X-W|^2) = a(1-a)|U-W|^2
  K3  K2 maximised over a in [0,1]: interior maximiser a = 1/2, value |U-W|^2/4 (NOT a simplex vertex)
  K4  a concave function need not maximise at a vertex: -(x-1/2)^2 elementary control
  K5  E_a is concave in a (verify symbolically: second derivative in a <= 0 for |U-W|^2 >= 0)

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/schur_stress_calibration.py
"""
import io
import sympy as sp

OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


# ---- K1: single edge, weights at a simplex vertex ----
a, Xx, Xy, Ux, Uy, Wx, Wy = sp.symbols('a Xx Xy Ux Uy Wx Wy', real=True)
X = sp.Matrix([Xx, Xy])
U = sp.Matrix([Ux, Uy])
W = sp.Matrix([Wx, Wy])
say("=== K1: simplex vertex (single edge, one free endpoint) ===")
E1 = sp.expand((U - X).dot(U - X))
sol1 = sp.solve([sp.diff(E1, Xx), sp.diff(E1, Xy)], [Xx, Xy], dict=True)[0]
say("  min_X |U-X|^2 attained at X = U ; value = %s  (free endpoint coincides with the anchor)"
    % sp.simplify(E1.subs(sol1)))

# ---- K2: two-edge path, weights (a, 1-a) ----
say("")
say("=== K2: two-edge path U - X - W with weights (a, 1-a) ===")
E2 = sp.expand(a * (U - X).dot(U - X) + (1 - a) * (X - W).dot(X - W))
sol2 = sp.solve([sp.diff(E2, Xx), sp.diff(E2, Xy)], [Xx, Xy], dict=True)[0]
say("  stationary X = %s" % [sp.simplify(sol2[Xx]), sp.simplify(sol2[Xy])])
say("  (expected: the weighted average a*U + (1-a)*W)")
val2 = sp.simplify(E2.subs(sol2))
say("  E_a(U) = %s" % sp.factor(sp.simplify(val2)))
say("  (expected: a*(1-a)*|U-W|^2)")

# ---- K3: maximise over a ----
say("")
say("=== K3: max over a in [0,1] of E_a ===")
s = sp.symbols('s', nonnegative=True)          # s = |U-W|^2
expr = sp.expand(a * (1 - a) * s)
crit = sp.solve(sp.diff(expr, a), a)
say("  critical point a* = %s" % crit)
say("  value at a*=1/2: %s ; at the vertices a=0,1: 0" % sp.simplify(expr.subs(a, sp.Rational(1, 2))))
say("  => the maximum over the simplex is INTERIOR (a = 1/2): value |U-W|^2/4 > 0, whereas every")
say("     simplex vertex gives 0.  The finite-vertices route is therefore WRONG and is retracted.")

# ---- K4: elementary concave control ----
say("")
say("=== K4: concave functions need not maximise at vertices ===")
x = sp.symbols('x', real=True)
f = -(x - sp.Rational(1, 2)) ** 2
say("  f(x) = -(x-1/2)^2 on [0,1]: f'' = %s <= 0 (concave) ; max at x = 1/2 (interior) with f = %s ;"
    % (sp.diff(f, x, 2), sp.simplify(f.subs(x, sp.Rational(1, 2)))))
say("  endpoints f(0) = f(1) = %s" % sp.simplify(f.subs(x, 0)))

# ---- K5: concavity of E_a in a ----
say("")
say("=== K5: E_a concave in a ===")
d2 = sp.simplify(sp.diff(expr, a, 2))
say("  d^2/da^2 [a(1-a)|U-W|^2] = %s (<= 0 for |U-W|^2 >= 0)" % d2)
say("")
say("Lagrangian route (lead, to be written as the proof):")
say("  L = t + sum_e alpha_e (|edge_e|^2 - t); inf_t forces sum_e alpha_e = 1;")
say("  inf over the free nodes gives E_alpha(U) = min_X sum_e alpha_e |edge_e|^2 (concave, nonlinear in alpha);")
say("  Slater => V(U)^2 = max_{alpha in simplex} E_alpha(U), a concave maximisation with interior optima.")
io.open('research-2026/team-current/r20-geometry/schur_stress_calibration.out.txt', 'w',
        encoding='utf-8').write("\n".join(OUT) + "\n")
print()
print("wrote schur_stress_calibration.out.txt")
