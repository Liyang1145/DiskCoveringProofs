"""Verify whole radial intervals for arbitrary normalized covers with 16 or 17 owners."""
import argparse
from decimal import Decimal
from fractions import Fraction as F
import json
from pathlib import Path

from polar_tables import OUTER_CAPS, R, SCALE, TURN, beta, radial_roles
from weighted_rings import verify_weighted_rings


def verify(source):
    records=json.loads(source.read_text(encoding="utf-8"),parse_float=Decimal)
    by_b={}
    for p in records:
        b=p["b"]
        lo,hi,s,count=(p[key] for key in ("low","high","core","count"))
        conditional=p.get("conditional_count",False)
        if b not in (14,16,17) or not SCALE-R<=lo<hi<=OUTER_CAPS[b] or not 0<s<lo-R:
            raise ValueError("invalid scope for radial proposal")
        if s<=2*R or not 1<=count<27-b:
            raise ValueError("insufficient support for the core disk count")
        if not conditional and 2*(count-1)*beta(s,s-R,s+R)>=TURN:
            raise ValueError("unproved lower bound on the core disk count")
        roles=radial_roles(b,lo,hi,s,count)
        if len(roles)!=len(p["classes"]) or any(list(x)!=y for x,y in zip(roles,p["classes"])):
            raise ValueError("radial roles disagree with the geometric reduction")
        weights=p["rings"]
        if not weights or any(not (0<x<=SCALE and w>0) for x,w in weights):
            raise ValueError("invalid circle weights")
        cases=[(m,a,h,F(cap)+(F(8,100_000) if outer or a>0 else F(5,10_000)),outer)
               for (m,a,h,outer),cap in zip(roles,p["caps"])]
        if len(cases)!=len(roles):
            raise ValueError("missing support cap")
        boxes=verify_weighted_rings(R,weights,cases)
        print(f"PASS B={b} D0 in [{lo}, {hi}]/1e9, {sum(boxes)} radial boxes"
              + (f" with at least {count} core-reaching disks." if conditional else "."))
        if not conditional:
            by_b.setdefault(b,[]).append((lo,hi))
    for b,intervals in sorted(by_b.items()):
        high=OUTER_CAPS[b]
        for lo,hi in sorted(intervals,reverse=True):
            if lo<=high<=hi:
                high=lo
        print(f"B={b} certified upper bound: D0 < {high}/1e9 (or lower).")


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("source",type=Path)
    a=p.parse_args()
    verify(a.source)
