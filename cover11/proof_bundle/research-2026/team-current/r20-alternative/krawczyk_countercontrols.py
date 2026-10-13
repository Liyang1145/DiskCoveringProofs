# -*- coding: utf-8 -*-
"""
r20-alternative / Krawczyk kernel: generic certificate spec + known countercontrols (exact rationals).

Operator (standard, n-dim):
    K(X) := x0 - Y*F(x0) + (I - Y*J(X)) * (X - x0)
with X = [X_lo, X_hi] an interval box, x0 = mid(X) (or x0 in X), Y a real n x n matrix
(typically an approximate inverse of J(x0)), J(X) an INTERVAL enclosure of the Jacobian over X, and
    (X - x0) := [X_lo - x0, X_hi - x0]          <-- the FULL interval difference.
It is symmetric iff x0 = mid(X).  Do NOT replace it by the radius, by [0, X_hi - x0], or by a point.

Theorems
 (T1 existence)  K(X) subset int(X)  =>  F has at least one zero in X.
      proof: phi(x) := x - Y F(x) maps X into K(X) (mean-value form
      F(x) - F(x0) in J(X)(x - x0)), hence into int(X) subset X, so phi: X -> X continuous =>
      Brouwer fixed point => F(x*) = 0 (Y nonsingular).
 (T2 uniqueness)  || I - Y J(X) || < 1 in a consistent matrix norm
      =>  at most one zero in X.
      proof: two zeros x*,y* in X  =>  x* - y* = (I - Y J(xi)) (x* - y*) with xi on the segment, so
      ||x*-y*|| <= ||I - YJ(X)|| * ||x*-y*|| < ||x*-y*|| unless x* = y*.
 (T3 both)  K(X) subset int(X)  AND  ||I - Y J(X)||_inf < 1  =>  unique zero in X
      (Banach: g := phi is a self-map of X and a q-contraction with q = ||I - YJ(X)||_inf < 1).
NOTE: T1 alone does NOT give uniqueness, and T2 alone does NOT give existence.

Countercontrols below use F(x) = x^2 + 1 (NO real zero) on X = [1/10, 3], x0 = 31/20, Y = 10/31.
"""
from fractions import Fraction as F

# --- exact rational interval helpers (1D) ---
def mul(a, b):
    p = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return (min(p), max(p))


def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[1], a[1] - b[0])
def subI(a, b): return (a[0] - b, a[1] - b)


X_lo, X_hi = F(1, 10), F(3)
x0 = (X_lo + X_hi) / 2
Y = F(10, 31)                              # approximate 1/J(x0); J(x) = 2x => J(x0) = 31/10
F0 = x0 * x0 + 1                           # F(x0)
JX = (2 * X_lo, 2 * X_hi)                  # J(X) = 2X = [1/5, 6]
disp_sym = (X_lo - x0, X_hi - x0)          # symmetric full difference = [-29/20, 29/20]
disp_one = (F(0), X_hi - x0)               # WRONG: one-sided
print("F(x) = x^2 + 1 (no real zero), X = [1/10, 3], x0 = %s, Y = %s, F(x0) = %s" % (x0, Y, F0))
print("J(X) = %s ; symmetric displacement = %s" % (JX, disp_sym))

# (a) correct Krawczyk: interval Jacobian + symmetric displacement
IminusYJX = sub((F(1), F(1)), mul((Y, Y), JX))
Kcorr = add(subI((x0, x0), Y * F0), mul(IminusYJX, disp_sym))
print("\n(a) correct     : I - YJ(X) = %s ; K(X) = %s" % (IminusYJX, Kcorr))
print("    K(X) subset int(X) ?  %s   (correctly FAILS: no zero exists)"
      % (Kcorr[0] > X_lo and Kcorr[1] < X_hi))

# (b) point-Jacobian version (J evaluated at x0 only): spurious contraction factor 0
IminusYJ0 = F(1) - Y * (2 * x0)
Kpoint = add(subI((x0, x0), Y * F0), mul((IminusYJ0, IminusYJ0), disp_sym))
print("\n(b) point-Jacob : I - YJ(x0) = %s ; K_p(X) = %s  -> subset int(X) ?  %s   <-- FALSE PASS"
      % (IminusYJ0, Kpoint, Kpoint[0] > X_lo and Kpoint[1] < X_hi))

# (c) ZERO displacement (treat X - x0 as the point (0,0)): same failure mode as (b)
Kzero = add(subI((x0, x0), Y * F0), mul(IminusYJX, (F(0), F(0))))
print("\n(c) zero-disp   : K_0(X) = %s  -> subset int(X) ?  %s   <-- FALSE PASS"
      % (Kzero, Kzero[0] > X_lo and Kzero[1] < X_hi))
print("    CORRECTED (lead team-message-cee607fe): a one-sided displacement is NOT generally harmless;")
print("    it is harmless only in special cases (e.g. E containing the symmetric 0).  See the 2D control (f).")

# (d) norms
print("\n(d) contraction: |I - YJ(X)|_inf (interval max abs) = %s < 1 ? %s ; point version gives 0 (spurious)"
      % (max(abs(IminusYJX[0]), abs(IminusYJX[1])), max(abs(IminusYJX[0]), abs(IminusYJX[1])) < 1))

# (e) positive control with an actual zero: F(x) = x^2 - 2 on X = [1, 2]
Xl, Xh = F(1), F(2)
x0b = (Xl + Xh) / 2
Yb = F(1, 3)                               # J(x0b) = 2*x0b = 3
F0b = x0b * x0b - 2
Imb = sub((F(1), F(1)), mul((Yb, Yb), (2 * Xl, 2 * Xh)))
Kb = add(subI((x0b, x0b), Yb * F0b), mul(Imb, (Xl - x0b, Xh - x0b)))
print("\n(e) positive ctrl F(x)=x^2-2, X=[1,2], x0=%s, Y=1/3 : I-YJ(X) = %s" % (x0b, Imb))
print("    K(X) = %s  subset int(X) ? %s ; q = %s < 1 ? %s  => existence (T1) + uniqueness (T2/T3) of the zero sqrt(2)"
      % (Kb, Kb[0] > Xl and Kb[1] < Xh, max(abs(Imb[0]), abs(Imb[1])), max(abs(Imb[0]), abs(Imb[1])) < 1))
# (f) 2D sign-cancelling control (lead's construction): E = [[a,-a],[a,-a]], A = I-E, F(x) = A x - b, Y = I
a = F(2)
E2 = [[a, -a], [a, -a]]
A2 = [[(F(1) if i == j else F(0)) - E2[i][j] for j in range(2)] for i in range(2)]
b = (F(3, 4), F(1, 4))
rad2 = F(1)                                   # X = [-1,1]^2, x0 = (0,0)
detA = A2[0][0] * A2[1][1] - A2[0][1] * A2[1][0]
Ainv = [[A2[1][1] / detA, -A2[0][1] / detA], [-A2[1][0] / detA, A2[0][0] / detA]]
root = (Ainv[0][0] * b[0] + Ainv[0][1] * b[1], Ainv[1][0] * b[0] + Ainv[1][1] * b[1])


def mulI_vec(M, vlo, vhi):
    """interval matrix * interval vector, exact rationals."""
    out = []
    for row in M:
        lo_ = sum(min(row[j] * vlo, row[j] * vhi) for j in range(len(row)))
        hi_ = sum(max(row[j] * vlo, row[j] * vhi) for j in range(len(row)))
        out.append((lo_, hi_))
    return out


print("\n(f) 2D control (lead cee607fe): E=[[2,-2],[2,-2]], A=I-E (det=%s), F=A x - b, Y=I, X=[-1,1]^2" % detA)
print("    true root x* = A^{-1} b = %s  -> OUTSIDE X  (A invertible, exactly one root)" % (root,))
print("    E*(r,r) with r=(1,1): %s   (rows cancel!)" % (E2[0][0] * 1 + E2[0][1] * 1,))
K_old = (b[0] + 0, b[1] + 0)                  # POINT radius / zero displacement: E*(r,r) = 0
print("    (f1) POINT radius: K = b = %s  -> subset int X ? %s   <-- FALSE PASS"
      % (K_old, abs(K_old[0]) < rad2 and abs(K_old[1]) < rad2))
K_one = mulI_vec(E2, F(0), rad2)              # single-sided interval [0,r]^2
K_one = [(b[0] + K_one[0][0], b[0] + K_one[0][1]), (b[1] + K_one[1][0], b[1] + K_one[1][1])]
print("    (f2) SINGLE-SIDED [0,r]^2 is NOT the point r: E*[0,1]^2 = [%s, %s] (width 2*a*r = 4)"
      % (K_one[0][0] - b[0], K_one[0][1] - b[0]))
print("         K = %s  -> subset int X ? %s   <-- correctly FAILS here (distinct from (f1))"
      % (K_one, all(q[0] > -rad2 and q[1] < rad2 for q in K_one)))
Ksym = mulI_vec(E2, -rad2, rad2)
Ksym = [(b[0] + Ksym[0][0], b[0] + Ksym[0][1]), (b[1] + Ksym[1][0], b[1] + Ksym[1][1])]
print("    symmetric interval K = %s  -> subset int X ? %s   (correctly FAILS)" % (Ksym, all(q[0] > -rad2 and q[1] < rad2 for q in Ksym)))
print("    |E|_inf = %s > 1 so the plain infinity-norm test also fails here." % (abs(a) + abs(-a)))

print("\nSUMMARY: the kernel must use (i) the INTERVAL Jacobian over X and (ii) the SYMMETRIC full")
print("displacement [X_lo - x0, X_hi - x0].  The POINTIZATION shortcuts (point Jacobian; point/zero")
print("displacement; point radius) turn a correct FAIL into a FALSE PASS (1D: F(x)=x^2+1; 2D (f1)).")
print("The SINGLE-SIDED interval [0,r]^2 is a DIFFERENT variant: it is not the point r (f2: E*[0,1]^2 =")
print("[-2,2], width 2*a*r, half of the symmetric width 4*a*r); in the 2D control it fails correctly,")
print("but it is only 'half-width' in general, so it must be kept strictly separate from (f1).")
print("On uniqueness: ||I - Y J(X)||_inf < 1 IS a valid contraction certificate for uniqueness (kept);")
print("the symmetric centered-box inclusion also yields uniqueness via the standard weighted-norm route.")




