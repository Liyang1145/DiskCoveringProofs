"""Lead's proposed sector factor constraint.

Setup.  Chord endpoints P,Q at distance R*u, R*v from a site c (both on the unit
circle in the reduced model), alpha = angle at c.  Then
   chord      d = R sqrt(q),  q = u^2+v^2-2uv cos alpha
   midpoint   M = (P+Q)/2,  |M|^2 = kappa^2 = 1 - R^2 q/4
   inward height  H = distance from c to the chord line, signed (positive when c
                      and the origin are on the same side).
   c = M + (l_P - H) n   with  l_P = (1 - u v cos alpha)/sqrt(q)   (bisector-axis
                      coordinate of the unit-circle point at distance R sin(alpha'
                      from both endpoints).
Hence   |c|^2 = kappa^2 + (l_P - H)^2  and the inward-root condition |c|<=sqrt(1-R^2)
is equivalent to
   (H - l_P)^2 <= 1 - R^2 - kappa^2 = R^2(1+uv cos alpha),
i.e. (for H on the origin side, H >= 0)
   R^2 (1 + u v cos alpha) <= 2 sqrt(1 - R^2 q/4) H .
Test: (a) is the identity exact; (b) is the inequality always satisfied in the
*feasible* domain |c| <= sqrt(1-R^2) (it must be, trivially); (c) is it satisfied
on the whole kernel box [0,pi]x[0,1]^2 (the lead's literal question)?
"""
import math, json
from pathlib import Path
R = 0.38; R2 = R*R
P = Path(__file__).parent

def pieces(u, v, a):
    q = u*u+v*v-2*u*v*math.cos(a)
    if q <= 1e-14: return None
    s = math.sqrt(q); kap = math.sqrt(max(0.0, 1 - R2*q/4))
    lP = (1 - u*v*math.cos(a))/s
    return q, s, kap, lP

def site_norm2(u, v, a, H):
    """|c|^2 for a site at inward height H (signed, origin side positive)."""
    pc = pieces(u, v, a)
    if pc is None: return None
    q, s, kap, lP = pc
    return kap*kap + (lP - H)**2

def closure_test_grid(N=120):
    worst_box = (+1e9,); worst_feas = (+1e9, 0, 0, 0, 0, 0, 0, 0, 0); nviol_feas = 0; best_margin = None
    for ia in range(N+1):
        a = math.pi*ia/N
        for iu in range(N+1):
            u = iu/N
            for iv in range(N+1):
                v = iv/N
                pc = pieces(u, v, a)
                if pc is None: continue
                q, s, kap, lP = pc
                H = R*u*v*math.sin(a)/s
                lhs = R2*(1+u*v*math.cos(a)); rhs = 2*kap*H
                slack = rhs - lhs
                if slack < worst_box[0]: worst_box = (slack, a, u, v, q, H, kap, lP)
                feas = site_norm2(u, v, a, H)
                ok = feas is not None and feas <= 1 - R2 + 1e-15
                if ok:
                    if slack < worst_feas[0]: worst_feas = (slack, a, u, v, q, H, kap, lP, feas)
                    if slack < 0: nviol_feas += 1
                # feasible-domain margin: compare the two equivalent forms
                rhs2 = 1 - R2 - kap*kap
                if best_margin is None or (lhs - rhs2) < best_margin[0]:
                    best_margin = (lhs - rhs2, a, u, v, lhs, rhs2)
    print('=== literal kernel box (no feasibility filter) ===')
    print('   worst slack %.6f at alpha=%.4f u=%.4f v=%.4f q=%.4g H=%.6f' % (worst_box[:5]+worst_box[5:6]))
    print('=== feasible domain |c|^2 <= 1-R^2 ===')
    print('   worst slack %.3e at alpha=%.4f u=%.4f v=%.4f q=%.4g H=%.6f |c|^2=%.6f'
          % (worst_feas[0], worst_feas[1], worst_feas[2], worst_feas[3], worst_feas[4], worst_feas[5], worst_feas[8]))
    print('   violations:', nviol_feas)
    print('=== identity lhs vs 1-R^2-kappa^2 (max excess) ===')
    print('   max(lhs - (1-R^2-kappa^2)) = %.3e' % best_margin[0])

if __name__ == '__main__':
    closure_test_grid()
    print()
    print('=== (d) worst slack over the LIPSCHITZ-feasible domain alpha <= acos(uv) ===')
    worst = (+1e9, 0, 0, 0, 0, 0, 0)
    worst_gen = (+1e9, 0, 0, 0, 0, 0, 0)
    for ia in range(361):
        a = math.pi*ia/360
        for iu in range(1, 101):
            u = iu/100
            for iv in range(1, 101):
                v = iv/100
                if u*v > 1: continue
                if a > math.acos(min(1.0, u*v)) + 1e-12: continue   # Lipschitz-feasible
                pc = pieces(u, v, a)
                if pc is None: continue
                q, s, kap, lP = pc
                H = R*u*v*math.sin(a)/s
                slack = 2*kap*H - R2*(1+u*v*math.cos(a))
                if slack < worst[0]: worst = (slack, a, u, v, H, lP, kap)
                # genuine-configuration filter: a switch at radius <= R actually exists,
                # i.e. H <= lP (site inside D_root) -- by construction H<=lP iff |c|^2<=1-R^2
                if H <= lP + 1e-15 and slack < worst_gen[0]:
                    worst_gen = (slack, a, u, v, H, lP, kap)
    print('   worst slack (alpha <= acos uv): %.6f at alpha=%.4f u=%.4f v=%.4f H=%.5f lP=%.5f kap=%.5f' % worst)
    print('   worst slack (further |c|^2<=1-R^2): %.3e at alpha=%.4f u=%.4f v=%.4f H=%.5f lP=%.5f' % worst_gen[:6])
    print()
    print('=== (e) is lP >= 0 for all Lipschitz-feasible (u,v,alpha)? ===')
    mn = (+1e9, 0, 0, 0)
    for ia in range(361):
        a = math.pi*ia/360
        for iu in range(1, 101):
            u = iu/100
            for iv in range(1, 101):
                v = iv/100
                if a > math.acos(min(1.0, u*v)) + 1e-12: continue
                pc = pieces(u, v, a)
                if pc is None: continue
                if pc[3] < mn[0]: mn = (pc[3], a, u, v)
    print('   min lP = %.9f at alpha=%.4f u=%.4f v=%.4f' % mn)
