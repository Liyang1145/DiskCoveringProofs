import io, json
from fractions import Fraction as F
from mpmath import mp, mpf, sin, cos, asin, sqrt, pi as MP_PI

mp.dps = 60
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


L_lo = mpf("0.76")            # elementary lower bound: L = 2 asin(0.38) >= 2*0.38 = 0.76
L_hi = mpf("0.7796")          # L <= 2*0.3898 < 0.7796
say("elementary bounds for L = 2 asin(0.38):")
say("  asin(0.38) < pi/8 (since sin(pi/8) = %s > 0.38)  -> L < pi/4 = %s" % (mp.nstr(sin(MP_PI / 8), 12), mp.nstr(MP_PI / 4, 12)))
say("  L >= 2*0.38 = 0.76 ; L <= 2*0.3898 = 0.7796")
say("  => 2L < pi/2 (2-step spans short, cos > 0 rigorously); 4L < pi (cos decreasing on all k<=4 ranges)")
say("cosine bounds on span ranges:")
say("  cos(L)   >= cos(pi/4) = %s ; (60-dps value cos(0.7796) = %s)" % (mp.nstr(cos(MP_PI / 4), 12), mp.nstr(cos(mpf("0.7796")), 12)))
say("  cos(2L)  in (0, cos(1.52)] ; 60-dps cos(1.5592) = %s  (sign rigorously + via 2L < pi/2)"
    % mp.nstr(cos(mpf("1.5592")), 12))
say("  cos(3L)  <= cos(2.28) = %s < 0 ; 60-dps cos(2.3388) = %s   (3L >= 3*0.76 = 2.28 > pi/2)"
    % (mp.nstr(cos(mpf("2.28")), 12), mp.nstr(cos(mpf("2.3388")), 12)))
say("  cos(4L)  <= cos(3.04) = %s < 0 ; 60-dps cos(3.1184) = %s   (4L >= 3.04)"
    % (mp.nstr(cos(mpf("3.04")), 12), mp.nstr(cos(mpf("3.1184")), 12)))
say("")
say("diagnostics: cos(3L) <= cos(5*pi/7) = %s  (elementary, since 2.28 > 5pi/7 = %s)"
    % (mp.nstr(cos(5 * MP_PI / 7), 12), mp.nstr(5 * MP_PI / 7, 12)))
say("criterion summary: M_L = 2 sum c_ij cos(k_ij L) v v^T  with cos(L)>0.707, cos(2L) in (0,0.011),")
say("  cos(3L) <= -0.62, cos(4L) <= -0.99  -> M_L >= 0 requires nearest-neighbour dominance of the weights.")
say("  No general convexity of E is claimed (a single 3-step edge with c>0 makes H_E indefinite).")
io.open('research-2026/team-current/r20-geometry/fixed_switch_stress_bounds.out.txt', 'w', encoding='utf-8').write("\n".join(OUT) + "\n")
print()
print("wrote fixed_switch_stress_bounds.out.txt")
