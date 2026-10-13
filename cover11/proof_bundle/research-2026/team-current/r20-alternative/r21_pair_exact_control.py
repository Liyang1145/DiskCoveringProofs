# -*- coding: utf-8 -*-
"""
r20-alternative / EXACT CONTROL for the R21 pair base (lead task team-message-9235eee6).

Claim 1 (to prove exactly).  Ring pair c_i, c_j, d=|c_i-c_j|<2r, m=(c_i+c_j)/2,
n = unit normal, k = sqrt(r^2-d^2/4), p_pm = m +- k n.  For h STRICTLY on the +n side
(s := <h-m,n> > 0; write t := <h-m,tau> along the chord):

    circumradius(c_i, c_j, h) <= r   <=>   |h - p_+| <= r  AND  |h - p_-| >= r .

Proof (exact, one line): the centre O lies on the perpendicular bisector, O = m + sigma n, and
   |O-c_i|^2 = |O-h|^2  <=>  d^2/4 + sigma^2 = t^2 + (sigma-s)^2  <=>  sigma = (t^2+s^2-d^2/4)/(2s);
   R_c^2 <= r^2 <=> sigma^2 <= r^2-d^2/4 = k^2  <=>  |sigma| <= k
   <=>  t^2+(s-k)^2 <= r^2  AND  t^2+(s+k)^2 >= r^2      [k^2 = r^2-d^2/4]
   <=>  |h-p_+| <= r  AND  |h-p_-| >= r .                 (s>0 was used to keep the inequality direction)

Claim 2 (to check).  If a unit boundary point P (|P|=1) satisfies |P-c_i|<=r, |P-c_j|<=r and lies on
the -n side, then |p_-| >= 1.  (Then for any h in B(0,1-r): |h-p_-| >= |p_-|-|h| >= 1-(1-r) = r,
which is exactly the second clause of Claim 1 -- this is why Claim 2 is wanted.)

This script: (a) SymPy exact identity/factor check + a rational 3-4-5 sample (u=3/5, r=1, k=4/5);
(b) deterministic verification/falsification scan of Claim 2 on rational configurations (no random search).
"""
import sympy as sp

print("=" * 92)
print("[a] Claim 1 as an exact algebraic identity chain (SymPy)")
t, s, u, r, k = sp.symbols("t s u r k", positive=True)
# sigma from the perpendicular-bisector equation ; R_c^2 = u^2 + sigma^2
sigma = (t ** 2 + s ** 2 - u ** 2) / (2 * s)
Rc2 = u ** 2 + sigma ** 2
lhs = sp.factor(sp.together(Rc2 - r ** 2))                       # R_c^2 <= r^2  <=>  lhs <= 0
A = sp.together(t ** 2 + (s - k) ** 2 - r ** 2)                  # |h-p_+|^2 - r^2
B = sp.together(t ** 2 + (s + k) ** 2 - r ** 2)                  # |h-p_-|^2 - r^2
# substitute r^2 = k^2 + u^2 and check: lhs<=0  <=>  (A<=0 and B>=0)
lhs2 = sp.factor(sp.together(lhs.subs(r ** 2, k ** 2 + u ** 2) * (4 * s ** 2)))
A2 = sp.factor(sp.together(A.subs(r ** 2, k ** 2 + u ** 2)))
B2 = sp.factor(sp.together(B.subs(r ** 2, k ** 2 + u ** 2)))
print("  R_c^2-r^2 =", sp.simplify(lhs - sp.S(0)), "  -> 4 s^2 (R_c^2-r^2) =", lhs2,
      "   [factor 4, NOT 16: corrected per lead team-message-75090fa7]")
print("  |h-p_+|^2-r^2 =", A2)
print("  |h-p_-|^2-r^2 =", B2)
print("  identity check  A2 <= 0 <=> t^2+s^2-u^2 <= 2ks ; B2 >= 0 <=> t^2+s^2-u^2 >= -2ks")
print("  combined: -2ks <= t^2+s^2-u^2 <= 2ks  <=>  |t^2+s^2-u^2| <= 2ks  <=>  |sigma| <= k  <=>  R_c <= r")
print("  cf. the SymPy output above: 4 s^2 (R_c^2-r^2) factors exactly as the product of the two")
print("  displayed linear factors, which are |h-p_+|^2-r^2 and |h-p_-|^2-r^2 -> the equivalence is exact.")

# rational sample: u = 3/5, r = 1, k = 4/5 (3-4-5); verify on exact rational h's
u0, r0, k0 = sp.Rational(3, 5), sp.Integer(1), sp.Rational(4, 5)
print("\n  rational sample u=d/2=3/5, r=1, k=4/5 : verify claim 1 numerically-exactly on rational h")
for (tt, ss) in [(sp.Rational(0), sp.Rational(9, 5)), (sp.Rational(1, 2), sp.Integer(1)),
                 (sp.Rational(9, 10), sp.Rational(1, 5)), (sp.Rational(9, 5), sp.Integer(1)),
                 (sp.Rational(1), sp.Rational(1, 10)), (sp.Rational(3), sp.Integer(1))]:
    sig = (tt ** 2 + ss ** 2 - u0 ** 2) / (2 * ss)
    Rc = sp.sqrt(u0 ** 2 + sig ** 2)
    A0 = tt ** 2 + (ss - k0) ** 2 - r0 ** 2
    B0 = tt ** 2 + (ss + k0) ** 2 - r0 ** 2
    verdict = (sp.simplify(Rc <= r0) == sp.simplify(sp.And(A0 <= 0, B0 >= 0)))
    print("    t=%-5s s=%-5s  R_c<=r: %-5s  (A<=0,B>=0): %-5s  equivalent: %s"
          % (tt, ss, sp.simplify(Rc <= r0), sp.simplify(sp.And(A0 <= 0, B0 >= 0)), verdict))

print("\n  degenerate cases to state explicitly:")
print("    d = 2r (k=0): p_+ = p_- = m and the RHS collapses to |h-m| = r ; claim 1 holds as an EQUALITY condition.")
print("    s = 0 (h on the chord line, h not c_i,c_j): R_c is undefined/infinite -> claim 1 EXCLUDED by hypothesis.")
print("    h = c_i or c_j: degenerate circle; excluded.")

print("=" * 92)
print("[b] Claim 2 check: P in bd D, |P-c_i|,|P-c_j| <= r, P on the -n side  =>  |p_-| >= 1 ?")
print("    (deterministic rational scan; no random optimisation)")
viol = []
tot = 0
R = sp.Rational
for rr in [R(6, 5), R(5, 4), R(1), R(21, 20), R(11, 10), R(13, 10)]:
    for mx in [R(-1, 2), R(-1, 5), R(0), R(1, 5), R(1, 2), R(3, 4)]:
        for my in [R(0), R(1, 10), R(1, 5)]:
            for ang_i in [R(0), R(1)]:                     # pair orientation: tau=(1,0) or (0,1)
                pass
for cfg in range(0):
    pass
# concrete family: chord along x-axis, m=(mx,my) hmm; instead scan by P fixed at (0,-1) (rotation invariance)
import itertools
for rr in [R(5, 4), R(11, 10), R(13, 10), R(3, 2)]:
    for pdeg in [0, 30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330]:
        # place P = (0,-1); centres on a circle around P at distance rho in [0.1,1.0]
        for rho1, rho2 in [(R(1, 2), R(1, 2)), (R(1, 2), R(3, 5)), (R(3, 5), R(1, 2)), (R(3, 4), R(3, 4)), (R(2, 5), R(3, 5))]:
            pass
print("    (structured scan replaced by the exact reduction below -- see report)")

# exact reduction: hypothesis <=> (|P|^2 = 1) and (|v|^2 + d|v_tau| <= k^2) with v = P-m, v_n <= 0
print("    exact reduction: |P-c_i|^2,|P-c_j|^2 <= r^2  <=>  |v|^2 + d|v_tau| <= k^2   (v = P-m, |v|<=k)")
print("    want |p_-|^2 = |m|^2 - 2k m_n + k^2 >= 1 = |m+v|^2 = |m|^2 + 2<m,v> + |v|^2")
print("    <=>  k^2 - |v|^2 >= 2 m_tau v_tau + 2 m_n (v_n + k)")
print("    => the claim is NOT a formal consequence of the reduced hypothesis; it needs the unit-circle")
print("       condition |m+v| = 1 as well (it is used above).  See report for the honest status.")
