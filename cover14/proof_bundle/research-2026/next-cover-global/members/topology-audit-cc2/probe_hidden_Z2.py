"""Probe Z2: explicit hidden-owner construction and the ownership jump under outward clipping.

Construction.  Fix r=R=U.  Sites on a ring of radius a=0.90 at angles 2*pi*j/11 (j=1..10)
cover S^1 at r=R with positive arcs (verified: r_boundary_cover(0.90)=0.2879 < R).  Site 0 is
placed at distance 1-R EXACTLY along angle 0, i.e. c_0 = (1-R, 0).  Then:
  * |c_0| + R = 1, so site 0 is ACTIVE (its disk is internally tangent to S^1 at (1,0)),
  * its own boundary arc at radius R is the SINGLE POINT (1,0),
  * so its owned arc has length 0: site 0 is an ACTIVE NON-OWNER (a 'hidden' site).
  * (1,0) is a boundary triple point: sites 0, 1 and 10 all at distance R from it.
Then clip outward: domain D_(1+e), radius r+e, same centres.  Site 0's disk has |c_0| < 1 < 1+e
so it now meets the boundary circle in a POSITIVE-length arc, and (with the ring sites kept
fixed) site 0 owns a positive-length arc at (approximately) the same angular position.
So the positive-owner count jumps from 10 to 11 while the ACTIVE count is unchanged => the
sentence 'every hidden cell has no new boundary ownership' is false.

Reports, for a sequence of clip sizes e: |A|, |O|, the gained owners, and the max owned length
vs the bound 2 asin(r+e).
"""
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
R = 0.33173203427623414


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def scan(sites, r, samples=1440000):
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


def build(a=0.90, hidden=True):
    k = 11
    sites = [(a * math.cos(2 * math.pi * j / k), a * math.sin(2 * math.pi * j / k))
             for j in range(k)]
    if hidden:
        sites[0] = (1 - R, 0.0)
    return sites


def report(r, samples=720000):
    sites = build()
    own = scan(sites, r, samples)
    O = [i for i, o in enumerate(own) if o > 1e-12]
    A = [i for i, c in enumerate(sites) if math.hypot(*c) + r >= 1 - 1e-15]
    return dict(r=repr(r), nA=len(A), nO=len(O), O=O, A=A,
                maxlen=max(own), bound=2 * math.asin(r),
                hidden_owner_len=own[0],
                nonowner_active=[i for i in A if i not in O])


def main():
    out = []
    for e in (0.0, 1e-6, 1e-4, 1e-3, 5e-3):
        # clip outward: same centres, radius r+e, domain radius 1+e
        r = R + e
        row = report(r)
        row["eps"] = e
        out.append(row)
    # also: same-centre fixed radius R, but with the hidden site moved outward by tiny delta
    out2 = []
    for d in (0.0, 1e-7, 1e-5, 1e-3):
        sites = build()
        sites[0] = ((1 - R) + d, 0.0)
        own = scan(sites, R, 720000)
        O = [i for i, o in enumerate(own) if o > 1e-12]
        A = [i for i, c in enumerate(sites) if math.hypot(*c) + R >= 1 - 1e-15]
        out2.append(dict(delta=d, nA=len(A), nO=len(O), hidden_len=own[0],
                         nonowner_active=[i for i in A if i not in O]))
    rep = dict(clip=out, centre_delta=out2)
    (HERE / "evidence" / "probe-hidden-Z2.json").write_text(json.dumps(rep, indent=1),
                                                            encoding="utf-8")
    print(json.dumps(rep, indent=1))


if __name__ == "__main__":
    main()
