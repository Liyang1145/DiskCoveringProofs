"""r20-geometry: is the "unique equidistant point in the common arc" hypothesis of the
fan disk-intersection mechanism automatic, and what breaks when it fails?

Setting (mechanism scope): two ring disks of radius r whose centres lie in B(0,s),
s = sqrt(1-r^2); a common tie U in dD covered by both; radical line parametrised by
m + t n with m the centre midpoint; k = sqrt(r^2 - d^2/4); crossings of dD at t_- < 0 < t_+
(orientation fixed so that U = m + t_+ n).  Mechanism conclusions:
   (i) t_+ <= k  (U covered)      (ii) t_- < -k  (the other crossing is a common tie too)
   => p_in = m - k n in int D, p_out = m + k n not in int D.
Hypothesis of the lead's note: U is the UNIQUE equidistant point of the two coverage arcs
inside their common overlap (equivalently: the other crossing V is covered by at most one).

This script searches for pairs of disk centres (both in B(0,s)) for which the hypothesis
fails, i.e. V is covered by BOTH disks, and reports whether the mechanism's conclusion fails too.
No sweeps beyond this bounded grid; the point is a scope statement, not a statistical claim.
"""
from mpmath import mp, mpf, sin, cos, sqrt, pi as MP_PI, atan2
import json

mp.dps = 30
r = mpf(1) / 2
s = sqrt(1 - r * r)
U = (mpf(1), mpf(0))


def try_pair(rU, phi1, phi2):
    ci = (U[0] - rU * cos(phi1), U[1] - rU * sin(phi1))
    cj = (U[0] - rU * cos(phi2), U[1] - rU * sin(phi2))
    if sqrt(ci[0] ** 2 + ci[1] ** 2) > s or sqrt(cj[0] ** 2 + cj[1] ** 2) > s:
        return None
    d = sqrt((cj[0] - ci[0]) ** 2 + (cj[1] - ci[1]) ** 2)
    if d == 0 or d >= 2 * r:
        return None
    m = ((ci[0] + cj[0]) / 2, (ci[1] + cj[1]) / 2)
    nn = (-(cj[1] - ci[1]) / d, (cj[0] - ci[0]) / d)
    k = sqrt(r * r - d * d / 4)
    mn = m[0] * nn[0] + m[1] * nn[1]
    disc = mn ** 2 - (m[0] ** 2 + m[1] ** 2) + 1
    if disc <= 0:
        return None
    roots = [-mn + sqrt(disc), -mn - sqrt(disc)]
    # orientation: U must be the + crossing (U is equidistant => on the radical line)
    tU = (U[0] - m[0]) * nn[0] + (U[1] - m[1]) * nn[1]
    if tU < 0:
        nn = (-nn[0], -nn[1])
        roots = [-x for x in roots]
        tU = -tU
    tp, tm = max(roots), min(roots)
    pin = (m[0] - k * nn[0], m[1] - k * nn[1])
    pout = (m[0] + k * nn[0], m[1] + k * nn[1])
    nrm = lambda p: sqrt(p[0] ** 2 + p[1] ** 2)
    V = (m[0] + tm * nn[0], m[1] + tm * nn[1])
    dV_i = sqrt((V[0] - ci[0]) ** 2 + (V[1] - ci[1]) ** 2)
    dV_j = sqrt((V[0] - cj[0]) ** 2 + (V[1] - cj[1]) ** 2)
    return dict(ci=ci, cj=cj, d=d, k=k, tU=tU, tp=tp, tm=tm,
                V_covered_both=(dV_i <= r + mpf("1e-20") and dV_j <= r + mpf("1e-20")),
                tm_plus_k=tm + k, nin=nrm(pin), nout=nrm(pout),
                hold_ii=(tm < -k), hold_pin=(nrm(pin) < 1))


hits, tested = [], 0
for iR in range(1, 21):
    rU = r * mpf(iR) / 20
    for ip in range(0, 36):
        for jp in range(0, 36):
            phi1 = 2 * MP_PI * mpf(ip) / 36
            phi2 = 2 * MP_PI * mpf(jp) / 36
            res = try_pair(rU, phi1, phi2)
            if res is None:
                continue
            tested += 1
            if res["V_covered_both"]:
                hits.append(dict(rU=float(rU), phi1=float(phi1), phi2=float(phi2),
                                 d=float(res["d"]), k=float(res["k"]), tU=float(res["tU"]),
                                 tm=float(res["tm"]), tm_plus_k=float(res["tm_plus_k"]),
                                 nin=float(res["nin"]), nout=float(res["nout"]),
                                 hold_ii=bool(res["hold_ii"]), hold_pin=bool(res["hold_pin"]),
                                 ci=[float(x) for x in res["ci"]],
                                 cj=[float(x) for x in res["cj"]]))
print("tested %d admissible pairs (r=%.2f, s=%.4f); pairs with V covered by BOTH disks: %d"
      % (tested, float(r), float(s), len(hits)))
if hits:
    bad = [h for h in hits if not (h["hold_ii"] and h["hold_pin"])]
    print("of these, %d violate at least one mechanism conclusion:" % len(bad))
    for h in bad[:6]:
        print("   rU=%.3f phi=%.3f/%.3f d=%.4f k=%.4f t_-=%+.4f t_-+k=%+.4f |p_in|=%.4f |p_out|=%.4f"
              % (h["rU"], h["phi1"], h["phi2"], h["d"], h["k"], h["tm"], h["tm_plus_k"],
                 h["nin"], h["nout"]))
    print("   => uniqueness of the tie in the common arc is LOAD-BEARING: without it the")
    print("      mechanism's (ii) and p_in in int D can both fail.")
    # minimal explicit witness: the one with smallest |c| (closest to the inward-root regime)
    w = min(hits, key=lambda h: max(abs(h["ci"][0]) + abs(h["ci"][1]), abs(h["cj"][0]) + abs(h["cj"][1])))
    print("\n   explicit witness (r=%.2f): c_i=%s c_j=%s" % (float(r), [round(x, 6) for x in w["ci"]],
                                                             [round(x, 6) for x in w["cj"]]))
    print("     d=%.6f k=%.6f  t_-=%+.6f  t_-+k=%+.6f  |p_in|=%.6f  |p_out|=%.6f"
          % (w["d"], w["k"], w["tm"], w["tm_plus_k"], w["nin"], w["nout"]))
else:
    print("no adversarial pair found in this grid")
json.dump(dict(tested=tested, hits=hits[:40]), open("audit_tie_uniqueness.json", "w"), indent=1)
print("\nwrote audit_tie_uniqueness.json")
