# -*- coding: utf-8 -*-
"""
r20-alternative / exact rational controls for the CENTRAL COUPLING note (no sampling, no optimisation).

Data (all rational): r = 5 ; h_A = (6,0) ; ring sites c_a = (0,0), c_b = (6,6) (|h_A-c_a| = |h_A-c_b| = 6).
Constraints:  R_c(h_A, h_B, c_a) <= r  and  R_c(h_A, h_B, c_b) <= r  (the two central site triangles).

Exact criterion used (polynomial, no square roots):
   for P,Q,S with A1=|Q-S|^2, A2=|S-P|^2, A3=|P-Q|^2, X=cross(Q-P,S-P):
        R <= r   <=>   A1*A2*A3 <= 4*r^2*X^2      (non-collinear triples; X = 2*Area)
Crescent form (Claim 1, chord (h_A,c)): with m=(h_A+c)/2, n=perp(c-h_A)/d, k=sqrt(r^2-d^2/4), p_+-=m+-kn,
   on the +n side:  R<=r <=> |h-p_+| <= r and |h-p_-| >= r ; on the -n side: mirrored.
"""
from fractions import Fraction as F

r = F(5)
hA = (F(6), F(0))
ca = (F(0), F(0))
cb = (F(6), F(6))


def sub(a, b): return (a[0] - b[0], a[1] - b[1])
def dot(a, b): return a[0] * b[0] + a[1] * b[1]
def cross(a, b): return a[0] * b[1] - a[1] * b[0]
def n2(a): return dot(a, a)


def R2_leq_r2(P, Q, S, r):
    """exact test R_c(P,Q,S) <= r for non-collinear triples; returns (bool, certificates)."""
    A1, A2, A3 = n2(sub(Q, S)), n2(sub(S, P)), n2(sub(P, Q))
    X = cross(sub(Q, P), sub(S, P))
    lhs = A1 * A2 * A3
    rhs = 4 * r * r * X * X
    return (lhs <= rhs), dict(A1=A1, A2=A2, A3=A3, lhs=lhs, rhs=rhs, X=X, collinear=(X == 0))


def crescent(chord_p, chord_q, r):
    """returns m, n, k, d and p_+, p_- for the chord (chord_p, chord_q)."""
    d2 = n2(sub(chord_q, chord_p))
    d = None
    m = ((chord_p[0] + chord_q[0]) / 2, (chord_p[1] + chord_q[1]) / 2)
    # rational input -> keep d^2 only; k^2 = r^2 - d^2/4 ; we do exact sign tests with d^2
    return m, d2


def crescent_points(chord_p, chord_q, r):
    """for chords whose k is rational, returns the exact rational p_+, p_- (and the side normal)."""
    v = sub(chord_q, chord_p)
    d2 = n2(v)
    k2 = r * r - d2 / 4
    if k2 < 0:
        return None
    k = None
    # rational square root test
    num, den = k2.numerator, k2.denominator
    import math
    if math.isqrt(num) ** 2 != num or math.isqrt(den) ** 2 != den:
        return None                     # non-rational k: caller must use the polynomial test
    k = F(math.isqrt(num), math.isqrt(den))
    dv = None
    m = ((chord_p[0] + chord_q[0]) / 2, (chord_p[1] + chord_q[1]) / 2)
    w = (-v[1], v[0])
    # normalise w exactly (|v|^2 = d2 -> |v| rational iff d2 is a square)
    if math.isqrt(d2.numerator) ** 2 != d2.numerator or math.isqrt(d2.denominator) ** 2 != d2.denominator:
        return None
    dv = F(math.isqrt(d2.numerator), math.isqrt(d2.denominator))
    n = (w[0] / dv, w[1] / dv)
    return m, n, k, k2, dv


def crescent_test(h, chord_p, chord_q, r):
    """INDEPENDENT exact crescent test (uses the rational p_+- and the two clauses), no call to R2_leq_r2."""
    g = crescent_points(chord_p, chord_q, r)
    if g is None:
        return 'undefined (irrational k for this control)', ''
    m, n, k, k2, dv = g
    pp = (m[0] + k * n[0], m[1] + k * n[1])
    pm = (m[0] - k * n[0], m[1] - k * n[1])
    s = dot(sub(h, m), n)
    d_pp2 = n2(sub(h, pp))
    d_pm2 = n2(sub(h, pm))
    if s > 0:
        ok = (d_pp2 <= r * r) and (d_pm2 >= r * r)
        side = '+n (clause |h-p_+|<=r and |h-p_-|>=r)'
    elif s < 0:
        ok = (d_pm2 <= r * r) and (d_pp2 >= r * r)
        side = '-n (clause |h-p_-|<=r and |h-p_+|>=r)'
    else:
        return 'degenerate (h on the chord line)', 'collinear'
    return ('feasible' if ok else 'infeasible'), side + "  |h-p_+|^2=%s |h-p_-|^2=%s r^2=%s" % (d_pp2, d_pm2, r * r)


print("r =", r, " h_A =", hA, " c_a =", ca, " c_b =", cb)
print()
for name, hB in [("P1 h_B=(3,4)", (F(3), F(4))),
                 ("N1 h_B=(3,1/2)", (F(3), F(1, 2))),
                 ("X  h_B=(3,8)", (F(3), F(8))),
                 ("X  h_B=(9,1)", (F(9), F(1)))]:
    ok_a, ca_ = R2_leq_r2(hA, hB, ca, r)
    ok_b, cb_ = R2_leq_r2(hA, hB, cb, r)
    pa, sidea = crescent_test(hB, hA, ca, r)
    pb, sideb = crescent_test(hB, hA, cb, r)
    print("%-16s  tri_a: R<=r = %-5s (A1A2A3=%8s <= 4r^2X^2=%8s)   tri_b: R<=r = %-5s" %
          (name, ok_a, ca_["lhs"], ca_["rhs"], ok_b))
    print("                  crescent(chord h_A-c_a): %-10s side=%-12s  crescent(chord h_A-c_b): %-10s side=%s"
          % (pa, sidea, pb, sideb))

print("\n[contained-region control] K_B = closed disk B((3,4),1) : no boundary intersections with any")
print("  crescent circle, yet K_B is entirely feasible -> canonical witness = centre (3,4)")
cB, rB = (F(3), F(4)), F(1)
allok = True
for chord, tag in [((hA, ca), "chord h_A-c_a"), ((hA, cb), "chord h_A-c_b")]:
    m, n, k, k2, dv = crescent_points(chord[0], chord[1], r)
    pp = (m[0] + k * n[0], m[1] + k * n[1]); pm = (m[0] - k * n[0], m[1] - k * n[1])
    # uniform clauses for the whole disk K_B:
    #   K_B subset {|h-p| <= R'}  <=> |cB-p| + rB <= R'      (R' = r)
    #   K_B subset {|h-p| >= R'}  <=> |cB-p| - rB >= R'
    def inside(p):  return n2(sub(cB, p)) <= (r - rB) ** 2      # K_B subset {|h-p| <= r}
    def outside(p): return n2(sub(cB, p)) >= (r + rB) ** 2      # K_B subset {|h-p| >= r}
    s_cB = dot(sub(cB, m), n)
    ok = ((inside(pp) and outside(pm)) if s_cB > 0 else (inside(pm) and outside(pp)))
    allok = allok and ok
    print("   %-16s |cB-p_+|^2=%-6s |cB-p_-|^2=%-6s  s_cB=%-4s  disk inside the crescent: %s"
          % (tag, n2(sub(cB, pp)), n2(sub(cB, pm)), s_cB, ok))
print("   => K_B is entirely inside the feasible crescent of both chords; NO circle-boundary intersection")
print("      is needed to detect the non-empty intersection (contained-cell case), witness = centre (3,4).")
print("   overall contained-feasibility:", allok)
