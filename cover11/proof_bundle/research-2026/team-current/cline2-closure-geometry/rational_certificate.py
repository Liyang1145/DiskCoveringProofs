from fractions import Fraction as Q
from mpmath import mp, sin, cos, acos, sqrt, pi, mpf
mp.dps = 30

print("=== exact rational certificate ===")
print()
print("(C1) r(1 + sin 2b) <= (19/50)*(1 + sin 2) for r <= 19/50, b in [1, pi/2]")
print("     (sin 2b <= sin 2 on that range: d/db sin2b = 2cos2b <= 0 since 2b in [2,pi])")
S6 = Q(0)
term = Q(2)  # x = 2
# sin x alternating series: x - x^3/3! + x^5/5! - x^7/7! + x^9/9! - x^11/11!
for k in range(6):
    n = 2*k+1
    num = Q(2)**n
    import math
    den = math.factorial(n)
    S6 += (num/den) * (Q(1) if k % 2 == 0 else Q(-1))
print("     S_5(2) = sum_{k=0}^{5} (-1)^k 2^{2k+1}/(2k+1)! =", S6, "=", float(S6))
print("     alternating-series bound: 0 < sin 2 < S_5(2) ; S_5(2) < 91/100 ?",
      S6 < Q(91,100), "  (gap", float(Q(91,100)-S6), ")")
print("     so sin 2 < 91/100 and sin 2b <= sin 2 < 91/100")
print()
print("(C2) sqrt(2139)/50 in (924/1000, 925/1000):")
print("     50^2 * (924/1000)^2 =", Q(50)**2*Q(924,1000)**2, " < 2139 ?",
      Q(50)**2*Q(924,1000)**2 < 2139)
print("     2139 < 50^2*(925/1000)^2 =", Q(50)**2*Q(925,1000)**2, "?",
      2139 < Q(50)**2*Q(925,1000)**2)
print("     => sqrt(2139)/50 in (0.924, 0.925)")
print()
print("(C3) (19/50)*(1+91/100) < sqrt(2139)/50 :")
lhs = Q(19,50)*(1+Q(91,100))
print("     LHS =", lhs, "=", float(lhs))
print("     need (19/50)*(191/100) < sqrt(2139)/50  <=>  (19*191/100) < sqrt(2139)")
print("     <=>  36.29 < sqrt(2139)  <=>  36.29^2 =", Q(3629,100)**2, " < 2139 ?",
      Q(3629,100)**2 < 2139, " (gap", float(2139-Q(3629,100)**2), ")")
print()
print("(C4) conclusion: r(1+sin2b) <= (19/50)*(191/100) < sqrt(2139)/50 <= sqrt(1-r^2)")
print("     with strict gap > %.6f" % float(sqrt(2139)/50 - lhs))

print()
print("=== numeric sanity ===")
r = mpf(19)/50
print("  sqrt(1-r^2) =", mp.nstr(sqrt(1-r*r), 15), " ; sqrt(2139)/50 =", mp.nstr(sqrt(mpf(2139))/50, 15))
print("  r(1+sin2) =", mp.nstr(r*(1+sin(2)), 15))
print("  gap =", mp.nstr(sqrt(1-r*r) - r*(1+sin(2)), 12))

print()
print("=== the disk-v cap ===")
print("  (v,t) in D_j  =>  (v - r sin2b_j)^2 <= r^2  =>  v <= r(1 + sin2b_j)")
for (rr, bb) in [('0.375', '1'), ('0.38', '1'), ('0.38', '1.181')]:
    rrr = mpf(rr); bbb = mpf(bb)
    print("    r=%s b=%s : r(1+sin2b) = %.9f" % (rr, bb, rrr*(1+sin(2*bbb))))
