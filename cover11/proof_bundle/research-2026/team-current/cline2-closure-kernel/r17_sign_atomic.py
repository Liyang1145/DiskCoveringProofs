"""R17 atomic sign resolution: h(T) = -sin(2T), T in [2, 2 acos(0.375)], tau = 87/40.

Print the raw sequence so there is no room for a reduction bug.
"""
import math, sys

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
b_hi = math.acos(0.375)
T_lo, T_hi = 2.0, 2 * b_hi
print(f'acos(0.375) = {b_hi:.12f}')
print(f'T_lo={T_lo}, T_hi={T_hi:.12f}')
print(f'2*T_lo = {2*T_lo:.12f}, 2*T_hi = {2*T_hi:.12f}, pi = {math.pi:.12f}')
print(f'sin(2*T_lo) = {math.sin(2*T_lo):+.12f}; sin(2*T_hi) = {math.sin(2*T_hi):+.12f}')
print(f'h\'\'(T) = 4 sin(2T): at T_lo {4*math.sin(2*T_lo):+.9f}, at T_hi {4*math.sin(2*T_hi):+.9f}')

vals = [4 * math.sin(2 * (T_lo + (T_hi - T_lo) * k / 100000)) for k in range(100001)]
print(f'  min over grid = {min(vals):+.9f}  max over grid = {max(vals):+.9f}')
print(f'  sign of h\'\' everywhere: {"NEGATIVE (concave)" if max(vals) < 0 else "SOME POSITIVE"}')

TAU = 87 / 40
h = lambda T: -math.sin(2 * T)
hp = lambda T: -2 * math.cos(2 * T)
print(f'\ntau = {TAU}')
print(f'  2*tau = {2*TAU:.12f} (pi = {math.pi:.12f})')
print(f'  cos(2*tau) = {math.cos(2*TAU):+.12f}  -> h\'(tau) = {hp(TAU):+.12f}')
print(f'  h(tau) = {h(TAU):+.12f}')

mx = -1e18
mn = 1e18
argmx = argmn = None
for k in range(200001):
    T = T_lo + (T_hi - T_lo) * k / 200000
    d = h(T) - (h(TAU) + hp(TAU) * (T - TAU))
    if d > mx:
        mx, argmx = d, T
    if d < mn:
        mn, argmn = d, T
print(f'\nmax_T [h(T) - tangent(T)] = {mx:+.9e} at T={argmx:.9f}')
print(f'min_T [h(T) - tangent(T)] = {mn:+.9e} at T={argmn:.9f}')
print(f'=> tangent lies {"ABOVE" if mx <= 0 else "PARTLY BELOW"} h on the interval')
print(f'=> h(T) <= tangent for all T: {mx <= 1e-12}')

print('\nsanity at three points:')
for T in (T_lo, TAU, T_hi):
    d = h(T) - (h(TAU) + hp(TAU) * (T - TAU))
    print(f'  T={T:.9f}: h={h(T):+.9f} tangent={h(TAU)+hp(TAU)*(T-TAU):+.9f} diff={d:+.9e}')

print('\nliteral doc interval check: RIDGE-RANK-ONE-COUPLING.md says T in [2, 2acos(3/8)]')
print(f'  2acos(3/8) = {2*math.acos(0.375):.12f} = T_hi above  -> same interval')
print(f'  the doc also writes "2T in (pi,2pi)": 2T in ({2*T_lo:.6f},{2*T_hi:.6f}) '
      f'-> {2*T_lo > math.pi and 2*T_hi < 2*math.pi}')
