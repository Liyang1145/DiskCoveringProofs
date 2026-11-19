"""Anchored thirteen-disk exclusion at a proposed test radius."""
import argparse
from pathlib import Path

from polar_tables import TURN, SCALE, beta, bins, machins_formula, write_data

RADII=(
    120,145,170,192,215,235,253,272,292,311,326,338,348,363,381,400,424,449,
    474,498,521,545,570,596,622,648,678,713,750,792,837,887,941,975,1000,
)


def generate(path,r,band,angular,radial,first,last):
    machins_formula()
    if r>342_000_000 or r<330_000_000 or TURN%angular or angular%2:
        raise ValueError("test radius or grid outside auxiliary scope")
    start=SCALE-r
    end=943_000_000
    # 1.155 > 2/sqrt(3), by an exact square comparison.
    if 3*1155**2<=4*1000**2 or end*end<=SCALE*SCALE-r*r:
        raise ValueError("bad radial constants")
    maximum=(2155*r+999)//1000
    if 18*beta(SCALE,start,end,r)>=TURN:
        raise ValueError("nine boundary disks may suffice")
    split=2*r+1_000_000
    bands=((start,split),(split,maximum))
    lo,hi=bands[band]
    root=bins(lo,hi,max(4,radial//4))
    if not 0<=first<last<=len(root):
        raise ValueError("invalid root bins")
    low=root[first][0]
    core=low-r-1_000
    core_anchors=core>r
    radii=sorted(set(s*10**6 for s in RADII)|({core} if core_anchors else set()))
    index={s:i for i,s in enumerate(radii)}
    rings=[(s,angular if s==SCALE else angular//2) for s in radii]
    families=[root[first:last],bins(low,end,radial),bins(0,start,2*radial)]
    roles=[(0,1,-1,0)]
    roles.extend((1,0,index[SCALE],(2*i+1)*TURN//18) for i in range(9))
    if core_anchors:
        families.append(bins(core-r,min(start,core+r),2*radial))
        if 4*beta(core,core-r,min(start,core+r),r)>=TURN:
            raise ValueError("antipodal anchors are not separated")
        roles.extend(((3,0,index[core],0),(3,0,index[core],TURN//2),(2,0,-1,0)))
    else:
        roles.extend([(2,0,-1,0)]*3)
    cuts=[[(i,1)] for i in range(len(radii))]
    for s in (348,381,424,474,521,570,622):
        cuts.extend(([(index[SCALE],1),(index[s*10**6],1)],
                     [(index[SCALE],1),(index[s*10**6],2)]))
    write_data(path,r,angular,rings,families,roles,cuts,[(10,13,1,r)],maximum)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("output",type=Path)
    p.add_argument("--radius",type=int,default=337_000_000)
    p.add_argument("--band",type=int,choices=[0,1],default=0)
    p.add_argument("--angular",type=int,default=360)
    p.add_argument("--radial",type=int,default=96)
    p.add_argument("--first",type=int,default=0)
    p.add_argument("--last",type=int)
    a=p.parse_args()
    generate(a.output,a.radius,a.band,a.angular,a.radial,a.first,
             a.last if a.last is not None else max(4,a.radial//4))
