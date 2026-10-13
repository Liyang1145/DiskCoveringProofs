"""Probe Z3: is the hidden-owner configuration a LEGAL cover at some r<=U?

Configuration: 10 sites on a ring of radius a at the 11 angles 2*pi*j/11 (j=1..10), plus one
'hidden' site c_0=(1-r,0) whose closed disk is internally tangent to S^1 at (1,0) while
covering part of the interior.  Facts to establish:
  * the covering radius r* = max_{x in D} min_i |x-c_i| of this 14-site configuration,
  * whether c_0 is genuinely useful (its disk is not contained in the union of the others),
  * at r = r*: how many sites are active, how many own a positive-length S^1 arc, and whether
    c_0 is an active non-owner,
  * at r = r* + e (outward clip): whether c_0 becomes a positive owner while the active count
    is unchanged.

r* is computed by a fine polar grid + local refinement; this is a rigorous-enough numeric
calibration for auditing a claimed proof step (the claim under test is a universal statement,
so one legal configuration with a ownership jump refutes the proof step).
"""
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
U = 0.33173203427623414
RING = 11


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def build(a, r_hidden):
    sites = [(a * math.cos(2 * math.pi * j / RING), a * math.sin(2 * math.pi * j / RING))
             for j in range(1, RING)]
    sites.insert(0, (1 - r_hidden, 0.0))
    return sites


def covering_radius(sites, nr=700, nt=2600):
    worst = -1.0
    for i in range(nr + 1):
        rr = i / nr
        for j in range(nt):
            th = 2 * math.pi * j / nt
            x = (rr * math.cos(th), rr * math.sin(th))
            m = min(dist(x, c) for c in sites)
            if m > worst:
                worst = m
                arg = x
    # local refine around arg
    for step in (0.01, 0.002, 0.0004, 0.00008, 0.000016, 0.0000032):
        for dx in (-step, 0, step):
            for dy in (-step, 0, step):
                x = (arg[0] + dx, arg[1] + dy)
                if math.hypot(*x) > 1:
                    continue
                m = min(dist(x, c) for c in sites)
                if m > worst:
                    worst = m
                    arg = x
    return worst, arg


def scan(sites, r, samples=720000):
    own = [0] * len(sites)
    for k in range(samples):
        th = 2 * math.pi * k / samples
        x = (math.cos(th), math.sin(th))
        m = 1e9
        bi = -1
        for i, c in enumerate(sites):
            d = dist(x, c)
            if d < m:
                m = d
                bi = i
        if m <= r:
            own[bi] += 1
    return [o / samples * 2 * math.pi for o in own]


def main():
    res = []
    best = None
    for a in [0.80 + 0.01 * i for i in range(25)]:
        sites = build(a, U)
        cr, arg = covering_radius(sites, nr=380, nt=1400)
        if best is None or cr < best[1]:
            best = (a, cr, arg)
        res.append(dict(a=a, covering_radius=cr, arg=arg))
    a, cr, arg = best
    sites = build(a, U)
    out = dict(best_ring_radius=a, covering_radius=cr, arg=arg,
               radius_le_U=(cr <= U),
               coverage_scan=res)
    for tag, rr in (("at_r*", cr), ("r*+1e-6", cr + 1e-6), ("U", U), ("U+1e-6", U + 1e-6)):
        own = scan(sites, rr)
        O = [i for i, o in enumerate(own) if o > 1e-12]
        A = [i for i, c in enumerate(sites) if math.hypot(*c) + rr >= 1 - 1e-15]
        out[tag] = dict(r=rr, nA=len(A), nO=len(O), O=O, A=A,
                        hidden_site_active=(0 in A), hidden_site_owner=(0 in O),
                        hidden_len=own[0], maxlen=max(own), bound=2 * math.asin(rr))
    (HERE / "evidence" / "probe-hidden-Z3.json").write_text(json.dumps(out, indent=1),
                                                            encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "coverage_scan"}, indent=1))


if __name__ == "__main__":
    main()
