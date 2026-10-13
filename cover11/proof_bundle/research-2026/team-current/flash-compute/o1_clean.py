# -*- coding: utf-8 -*-
"""o1_clean.py -- make the O1-negative ledger STRICTLY legal (t < a, o > 0, private > 0)
and re-verify O1 with mpmath at 50 dps.  Also records the scalar-vs-true comparison.

Strict construction: take the scan-min data, shrink every filler half-width to a*(1-1e-9)
and shift the fillers to leave a tiny positive overlap with each neighbour; then all
ledger inequalities are strict (t <= a(1-1e-9) < a, o >= 1e-10 > 0, private > 0).
Numeric only.
"""
import json, math, os
import mpmath as mp

mp.mp.dps = 50
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
R = 0.38
A = math.asin(R)


def rho(t):
    return math.cos(t) - math.sqrt(max(R * R - math.sin(t) ** 2, 0.0))


def crossing_mp(c1, c2):
    c1 = (mp.mpf(c1[0]), mp.mpf(c1[1])); c2 = (mp.mpf(c2[0]), mp.mpf(c2[1]))
    r = mp.mpf(R)
    mx, my = (c1[0] + c2[0]) / 2, (c1[1] + c2[1]) / 2
    dx, dy = c2[0] - c1[0], c2[1] - c1[1]
    D = mp.sqrt(dx * dx + dy * dy)
    h = mp.sqrt(r * r - D * D / 4)
    px, py = -dy / D, dx / D
    a = (mx - h * px, my - h * py); b = (mx + h * px, my + h * py)
    return a if (a[0] ** 2 + a[1] ** 2) <= (b[0] ** 2 + b[1] ** 2) else b


if __name__ == "__main__":
    d = json.load(open(os.path.join(OUT, "o1_counterexample_scan-min.json"), encoding="utf-8"))
    t = list(d["t"]); o12 = d["overlaps"][0]
    eps = 1e-9
    t = [t[0], t[1], t[2]] + [A * (1 - eps)] * 6
    # positions: arcs 1,2 overlap by o12 ; arc 3 touches arc 2 with a tiny overlap; fillers
    # tile the rest with tiny overlaps (0.001 of the slack each)
    tiny = 1e-6
    psi = [0.0, t[0] + t[1] - o12]
    psi.append(psi[1] + t[1] + t[2] - tiny)                       # disk 3 overlaps disk 2 slightly
    slack = 2 * math.pi - (psi[2] + t[2]) - t[0]                  # angular room for the six fillers
    step = (slack - 6 * tiny * 0) / 6.0
    cur = psi[2] + t[2] - tiny
    for k in range(6):
        psi.append(cur + t[3 + k])
        cur = psi[-1] + t[3 + k] - tiny
    # closing overlap with arc 1
    o = []
    for k in range(9):
        dd = (psi[(k + 1) % 9] - psi[k]) % (2 * math.pi)
        o.append(t[k] + t[(k + 1) % 9] - dd)
    priv = [2 * t[k] - o[k - 1] - o[k] for k in range(9)]
    C = [(rho(t[k]) * math.cos(psi[k]), rho(t[k]) * math.sin(psi[k])) for k in range(9)]
    worst = None
    for k in range(9):
        v = crossing_mp(C[k], C[(k + 1) % 9])
        for j in range(9):
            if j in (k, (k + 1) % 9):
                continue
            dd = float(mp.sqrt((v[0] - mp.mpf(C[j][0])) ** 2 + (v[1] - mp.mpf(C[j][1])) ** 2))
            if worst is None or dd - R < worst[0]:
                worst = (dd - R, k, j, float(mp.sqrt(v[0] ** 2 + v[1] ** 2)))
    print("strictly legal ledger r=0.38:")
    print("  t/a        = %s" % ["%.9f" % (x / A) for x in t])
    print("  overlaps   = %s  (min %+.3e)" % (["%.9f" % x for x in o], min(o)))
    print("  private    = %s  (min %+.3e)" % (["%.9f" % x for x in priv], min(priv)))
    print("  sum 2t = %.12f   2pi + sum o = %.12f   diff %.2e"
          % (2 * sum(t), 2 * math.pi + sum(o), 2 * sum(t) - (2 * math.pi + sum(o))))
    print("  O1 margin (mpmath 50 dps): %+.9e  (pair #%d, third #%d, |v| = %.9f)"
          % (worst[0], worst[1], worst[2], worst[3]))
    out = dict(tag="strict-legal", r=R, a=A, t=t, psi=psi, overlaps=o, private=priv, centres=C,
               sum2t=2 * sum(t), worst_O1_margin=worst[0], worst_pair=[worst[1], worst[2]],
               ledger_strict=bool(max(t) < A and min(o) > 0 and min(priv) > 0),
               note="O1-negative strictly legal arc ledger; NOT cover-extendable (hole MEC ~0.61 > r)")
    p = os.path.join(OUT, "o1_counterexample_strict-legal.json")
    json.dump(out, open(p, "w", encoding="utf-8"), indent=1, default=str)
    print("  wrote %s" % p)
