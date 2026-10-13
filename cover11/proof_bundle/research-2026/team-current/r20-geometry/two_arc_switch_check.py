"""r20-geometry Round-11 (lead 2c68db35): bounded single test case for the two-arc switch, canonical domain.

Lead constraints honoured:
 * (2) exception: h = c covers the WHOLE circle (not a cap of half-angle pi/2); in our domain
   |c| >= rho > |h| so h != c and the cap formula applies -- the exception clause is now written out.
 * (4) the earlier construction used |c_i| = 0.95 > sqrt(1-r^2) ~ 0.925 -> it is NOT in the canonical
   inward domain; it is a boundary-cover OUTER-root configuration and is now labelled as such.
 * (5) one bounded test case only; if the vertex test already rejects, do not scale.

This script: canonical-domain configuration (r = 19/50, |c_i| = 0.92 <= sqrt(1-r^2) ~ 0.9250, nine rings
equally spaced 40 deg), our ring at angle 0, the splitting line y = 0 through the arc middle
x_mid = (0.54, 0).  We then report, for each side, (i) the ring-ring vertices in that side and
(ii) whether a single hub in H can cover them all (vertex test), plus the distance from the candidate's
hub positions to the arc.
Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/two_arc_switch_check.py
"""
import io
from mpmath import mp, mpf, cos, sin, sqrt, acos, atan2, pi as MP_PI
mp.dps = 40
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


r = mpf(19) / 50
rho = 1 - r
s_canon = sqrt(1 - r * r)
RC = mpf(92) / 100                      # |c_i| = 0.92 <= s_canon
say("r = %.6f ; rho = %.6f ; canonical inward bound sqrt(1-r^2) = %.6f ; |c_i| = %.6f" %
    (float(r), float(rho), float(s_canon), float(RC)))
say("(the earlier construction used |c_i| = 0.95 > %.6f -> outer-root / boundary-cover case, NOT canonical)"
    % float(s_canon))
n = 9
angles = [2 * MP_PI * k / n for k in range(n)]
centres = [(RC * cos(a), RC * sin(a)) for a in angles]
alpha = acos((RC ** 2 + 1 - r ** 2) / (2 * RC))
say("each ring covers a boundary arc of half-width alpha = %.4f deg ; spacing 40 deg ; margin = %+.4f deg"
    % (float(alpha * 180 / MP_PI), float((2 * alpha - 2 * MP_PI / n) * 180 / MP_PI)))
c0 = centres[0]
x_mid = (RC - r, mpf(0))
say("our ring c = (%.6f, 0) ; arc middle x_mid = (%.6f, 0)" % (float(c0[0]), float(x_mid[0])))

# ring-ring vertices (all pairs), keep those in D
V = []
for i in range(n):
    for j in range(i + 1, n):
        p1, p2 = centres[i], centres[j]
        dx, dy = p2[0] - p1[0], p2[1] - p1[1]
        d = sqrt(dx * dx + dy * dy)
        if d > 2 * r or d == 0:
            continue
        a = d / 2
        h = sqrt(r * r - a * a)
        mx, my = (p1[0] + p2[0]) / 2, (p1[1] + p2[1]) / 2
        ux, uy = dx / d, dy / d
        for sgn in (mpf(1), mpf(-1)) if h > 0 else (mpf(0),):
            x, y = mx - sgn * h * uy, my + sgn * h * ux
            if x * x + y * y <= 1:
                V.append((x, y))
say("ring-ring vertices inside D: %d" % len(V))
up = [v for v in V if v[1] >= -1e-12]
dn = [v for v in V if v[1] <= 1e-12]
say("upper side vertices: %d ; lower side: %d" % (len(up), len(dn)))


def max_pair(S):
    best = (mpf(0), None)
    for i in range(len(S)):
        for j in range(i + 1, len(S)):
            d = sqrt((S[i][0] - S[j][0]) ** 2 + (S[i][1] - S[j][1]) ** 2)
            if d > best[0]:
                best = (d, (i, j))
    return best


for name, S in (("upper", up), ("lower", dn)):
    dmax, pair = max_pair(S)
    say("  %s side: max pairwise vertex distance = %.6f vs 2r = %.6f -> single hub covering all vertices: %s"
        % (name, float(dmax), float(2 * r), "IMPOSSIBLE (vertex test rejects)" if dmax > 2 * r else "not excluded by this pair"))
say("")
say("candidate-style hubs (|h| ~ 0.15/0.27 near the origin) vs the arc: x_mid is at |x_mid| = %.6f, so a hub"
    % float(x_mid[0]))
say("with |h| <= 0.30 is at distance >= %.6f from x_mid; since that is BELOW r = %.6f, no impossibility follows"
    % (float(x_mid[0] - mpf("0.30")), float(r)))
say("from this crude bound -- the load-bearing reading of this test is the pairwise vertex rejection above.")
say("=> BOUNDED TEST OUTCOME: in this canonical-domain two-arc-switch configuration the vertex test already")
say("   REJECTS (a single side contains ring-ring vertices farther apart than 2r, so no one hub can cover them).")
say("   Per the lead's rule: do NOT scale this construction further; there is no test-level counterexample here.")
io.open('research-2026/team-current/r20-geometry/two_arc_switch_check.out.txt', 'w',
        encoding='utf-8').write("\n".join(OUT) + "\n")
print()
print("wrote two_arc_switch_check.out.txt")
