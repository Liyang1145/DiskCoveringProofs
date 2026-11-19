"""Exact verification of sums of angular capacities."""
from fractions import Fraction as F
from math import ceil

from polar_tables import PI_LO, SCALE, TURN, beta, machins_formula


def verify_weighted_rings(radius,rings,classes):
    """A class has multiplicity, radial range, cap, and optional boundary role."""
    machins_formula()
    total=sum(w for _,w in rings)
    caps=[ceil(F(c[3])*total*TURN/(2*PI_LO)) for c in classes]
    if sum(c[0]*cap for c,cap in zip(classes,caps))>=total*(TURN//2):
        raise ValueError("weighted upper bound does not contradict coverage")
    counts=[]
    for record,cap in zip(classes,caps):
        _,start,end,_=record[:4]
        outer=len(record)==4 or record[4]
        pending=[(start,end)]
        boxes=0
        if start>end:
            raise ValueError("empty radial class")
        while pending:
            lo,hi=pending.pop()
            boxes+=1
            upper=sum(w*max(0,beta(s,lo,hi,radius)) for s,w in rings if outer or s!=SCALE)
            if upper<=cap:
                continue
            if hi-lo<=1:
                raise ValueError(f"unresolved radius interval {(lo,hi)}")
            mid=(lo+hi)//2
            pending.extend(((lo,mid),(mid,hi)))
        counts.append(boxes)
    return counts
