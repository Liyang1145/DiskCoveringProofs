"""stress-audit step 10: domain / guard facts, all exact-rational or interval-rational.

  G1  L = 2 asin U < pi/4  (needed for dL<pi, d<=4)   via sin^2(pi/8)=(2-sqrt2)/4
  G2  9L > 2pi  (width simplex nonempty), via sin(pi/9) < pi/9 < 22/63 < U, pi < 22/7
  G3  cos(dL) = T_d(1-2U^2) exact rationals, d<=4
  G4  at the certified root box: 0 < 2beta < L and 0 < 2alpha < L (interiority of theta*)
      - 2beta < L  <=>  w^2(1-U^2) < 3 U^2 b^2
      - 2alpha < L <=>  A^2 < 12 U^2 S^2   (A>0)
  G5  box guards b>w (beta<pi/6), r<U, and all weight/divisor signs (from the kernel)
"""
from fractions import Fraction as F
from pathlib import Path
import json, sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.set_int_max_str_digits(10**6)
import step5_kernel as K

N12 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global")
U = F('0.361102963744508672616920293904')
U2 = U * U
res = {}

print("=== G1. 4L < pi  <=>  U < sin(pi/8)  <=>  sqrt2 < 2-4U^2 ===")
rhs = 2 - 4 * U2
print("  2-4U^2 =", float(rhs), ">0:", rhs > 0, "  (2-4U^2)^2-2 =", float(rhs * rhs - 2), ">0:", rhs * rhs - 2 > 0)
print("  => sqrt2 < 2-4U^2 <=> U^2 < (2-sqrt2)/4 = sin^2(pi/8) => asin U < pi/8 => L=2asin U < pi/4")
res['G1'] = {'rhs_positive': rhs > 0, 'rhs_sq_gt_2': rhs * rhs - 2 > 0}

print("\n=== G2. 9L > 2pi  (via U > 22/63 > pi/9 > sin(pi/9), pi<22/7) ===")
print("  U =", float(U), " > 22/63 =", float(F(22, 63)), ":", U > F(22, 63))
print("  pi/9 < 22/63 since pi < 22/7 (classical); sin(x) < x on (0,pi/2)")
res['G2'] = {'U_gt_22_63': U > F(22, 63)}

print("\n=== G3. exact rational cosine constants ===")
cosd = K.cos_table(U)
for d in (1, 2, 3, 4):
    print(f"  cos({d}L) = T_{d}(1-2U^2) = {float(cosd[d]):.15f}   sign {'+' if cosd[d] > 0 else '-'}")
res['G3'] = {d: str(v) for d, v in cosd.items()}

print("\n=== G4/G5. interiority and guards on the certified root box ===")
cert = json.loads((N12 / 'evidence/root-t-certificate.json').read_text(encoding='utf-8'))
box = [[str(F(s[0])), str(F(s[1]))] for s in cert['box']]
for grid in (10**60, 10**45):
    W = K.build(box, grid)
    b, w, S = W['b'], W['w'], W['S']
    A = 3 * b * b - w * w - 2 * b * w
    two_beta_ok = (w * w * (1 - U2)).hi < (3 * U2 * b * b).lo
    two_alpha_ok = (A * A).hi < (12 * U2 * S * S).lo if A.lo > 0 else None
    print(f"  grid 1e{len(str(grid))-1}: b>w: {b.lo > w.hi}   r<U: {W['r'].hi < U}   "
          f"A>0: {A.lo > 0}   2beta<L: {two_beta_ok}   2alpha<L: {two_alpha_ok}")
    print(f"      S-b<0: {S.hi < b.lo}   2a-t+r>0: {(2*W['a']-W['t']+W['r']).lo > 0}   "
          f"1-t^2-r^2>0: {(1-W['t']**2-W['r']**2).lo > 0}   2t-2r-a>0: {(2*W['t']-2*W['r']-W['a']).lo > 0}")
    wt = K.weights_of(W)
    print(f"      all weights>0: {all(v.lo > 0 for v in wt.values())}  W>0: {K.total(W).lo > 0}")
    res[f'G4_grid1e{len(str(grid))-1}'] = {'b_gt_w': b.lo > w.hi, 'r_lt_U': W['r'].hi < U,
                                           'A_pos': A.lo > 0, 'two_beta_lt_L': bool(two_beta_ok),
                                           'two_alpha_lt_L': bool(two_alpha_ok) if two_alpha_ok is not None else None,
                                           'S_minus_b_neg': S.hi < b.lo,
                                           '2a_t_plus_r_pos': (2 * W['a'] - W['t'] + W['r']).lo > 0,
                                           'one_minus_t2_r2_pos': (1 - W['t'] ** 2 - W['r'] ** 2).lo > 0,
                                           '2t_2r_a_pos': (2 * W['t'] - 2 * W['r'] - W['a']).lo > 0}

# candidate anchor gaps (ideal tiling): 6 gaps of 2beta, 3 gaps of 2alpha, sum 2pi
print("\n  tiling self-consistency at the box centre (exact rational):")
c = [(F(box[i][0]) + F(box[i][1])) / 2 for i in range(4)]
a_, t_, r_, w_ = c
b_ = (1 + a_ + r_) / 2
S_ = b_ * b_ + w_ * w_ / 3
print("    b,S rational (exact);  6*(2 beta) + 3*(2 alpha) = 2pi by the identity alpha = pi/3 - 2beta (construction)")
res['G6_centre'] = {'a': str(a_), 't': str(t_), 'r': str(r_), 'w': str(w_), 'b': str(b_), 'S': str(S_)}

(N12 / 'members/stress-audit/evidence/stress-audit-domain.json').write_text(json.dumps(res, indent=1), encoding='utf-8')
print("\nwrote evidence/stress-audit-domain.json")
