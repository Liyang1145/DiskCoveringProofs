"""Write outward-rounded angular capacities for the 14-owner search."""
import argparse
from fractions import Fraction as F
from math import acos, ceil, factorial, isqrt, pi
from pathlib import Path

TURN = 13_104_000_000
SCALE = 10**9
R = 230_796_000
END = 974_000_000
PI_LO = F("3.141592653589793238462643383279")
PI_HI = F("3.141592653589793238462643383280")
DEAD = -2*TURN
TRIG_SCALE = 10**19
COEFFICIENTS = tuple(-(-(-1)**j*TRIG_SCALE//factorial(2*j)) for j in range(12,-1,-1))
BANDS = (
    (812_000_000,835_000_000),
    (835_000_000,907_000_000),
    (907_000_000,918_879_000),
)
CORE_CAPS = {
    1:461_592_000, 2:461_592_000,
    3:498_000_000, 4:558_000_000, 5:624_000_000, 6:693_000_000, 7:693_000_000,
    8:750_000_000, 9:789_000_000, 10:831_000_000, 11:864_000_000, 12:871_000_000,
}
RADII = (
    145,165,185,205,222,237,255,275,296,318,340,365,390,415,440,465,490,515,
    538,560,582,604,625,645,665,680,699,715,731,749,769,797,832,875,925,967,1000,
)
INNER13_LOWER = 338_500_000
OUTER_NORM_UPPER = R + (R*SCALE+INNER13_LOWER-1)//INNER13_LOWER
OUTER_CAPS = {
    14:OUTER_NORM_UPPER,15:869_943_051,16:863_807_520,17:830_266_130,18:787_986_834,
}
B14_NORM_ORDER = (842_400_000,859_000_000,869_490_000,878_000_000,884_700_000,890_000_000)


def radial_roles(b,lo,hi,s,count):
    """Necessary norm ranges for outer, core-reaching and other disks."""
    inner=27-b
    first=[(lo,hi),(lo,min(END,2*OUTER_CAPS[b]-lo))]
    if b==18 and lo>=786_000_000:
        first.append((lo,845_000_000))
    classes=[(1,a,h,True) for a,h in first]
    classes.append((b-len(first),lo,END,True))
    for j in range(1,count+1):
        classes.append((1,s-R,min(s+R,CORE_CAPS[inner-1-count+j]),False))
    classes.append((inner-1-count,0,END,False))
    classes.append((1,0,R,False))
    return [c for c in classes if c[0]]


def machins_formula():
    def atan(q):
        x=F(1,q)
        low=sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(24))
        return low,low+x**49/49

    a,b=atan(5)
    c,d=atan(239)
    if not PI_LO<16*a-4*d or not 16*b-4*c<PI_HI:
        raise ValueError("bad pi enclosure")


def cosine_ticks(h):
    """Upper enclosure of cos(2*pi*h/TURN), scaled by TRIG_SCALE."""
    z=(2*PI_LO.numerator*h)**2*TRIG_SCALE//(PI_LO.denominator*TURN)**2
    # Keep both bounds in Horner's rule. The intermediate coefficients
    # have alternating signs, so a single upper bound on z is insufficient.
    l=COEFFICIENTS[0]-1
    u=COEFFICIENTS[0]
    for c in COEFFICIENTS[1:]:
        l,u=(min(l*z,l*(z+1))//TRIG_SCALE+c-1,
             -(-max(u*z,u*(z+1))//TRIG_SCALE)+c)
    return u


def beta(s,lo,hi,radius=R):
    """Upper half-angle in integer turns for an entire radial interval."""
    if lo>s+radius or hi<s-radius:
        return DEAD
    if lo==0 and s<=radius:
        return TURN//2
    a=s*s-radius*radius
    if hi*hi<=a:
        g=F(a+hi*hi,2*s*hi)
    elif lo*lo>=a:
        g=F(a+lo*lo,2*s*lo)
    else:
        precision=10**16
        g=F(isqrt(a*precision*precision),s*precision)
    if g>=1:
        return 0
    if g<=-1:
        return TURN//2
    guess=max(0,min(TURN//2,ceil(acos(float(g))*TURN/(2*pi))+1))
    h=guess
    while h<TURN//2 and cosine_ticks(h)*g.denominator>g.numerator*TRIG_SCALE:
        h=min(TURN//2,h+max(1,2*(h-guess)))
    return h


def bins(lo,hi,count):
    return [(lo+(hi-lo)*i//count,lo+(hi-lo)*(i+1)//count) for i in range(count)]


def check_anchors(core,count):
    # Radius 1, 13 regularly spaced test points, half a step off the axis.
    if beta(SCALE,SCALE-R,END)*26>=TURN:
        raise ValueError("outer anchors are not separated")
    if core<=2*R or beta(core,core-R,core+R)*2*count>=TURN:
        raise ValueError("core anchors are not separated")


def write_tables(path,band,angular,radial,first,last,phase=None,slot=None,
                 radial_window=None,core_count=None):
    low,high=BANDS[band]
    if radial_window is not None:
        low,high=radial_window
        if not BANDS[band][0]<=low<high<=BANDS[band][1]:
            raise ValueError("radial window outside the selected band")
    if not TURN%angular==0 or angular%2 or radial<4:
        raise ValueError("unsupported grid")
    machins_formula()
    root=bins(low,high,max(3,radial//4))
    if not 0<=first<last<=len(root):
        raise ValueError("invalid closed root interval")
    low=root[first][0]
    core=low-R-1_000
    arc=beta(core,core-R,core+R)
    core_disks=(TURN//2+arc-1)//arc
    count=(TURN-1)//(2*arc)
    if not 7<=count<=9 or not count<core_disks<=12 or TURN%count:
        raise ValueError("unsupported core anchor count")
    check_anchors(core,count)
    exact_core=core_count is not None
    if R*SCALE<=342_000_000*core and core_disks==10:
        if core_count is not None and core_count!=10:
            raise ValueError("contradicts the auxiliary thirteen-disk count")
        exact_core=True
    if core_count is not None:
        if not core_disks<=core_count<=12:
            raise ValueError("impossible specified core count")
        core_disks=core_count
    exactly_ten=exact_core and core_disks==10
    if (phase is None)!=(slot is None) or (phase is not None and not exactly_ten):
        raise ValueError("phase and slot require the exact ten-core-owner case")

    radii=sorted(set(s*10**6 for s in RADII)|{core})
    ring_id={r:i for i,r in enumerate(radii)}
    rings=[(r,angular if r==SCALE else angular//2) for r in radii]
    families=[
        root[first:last],
        bins(low,END,radial),
        bins(core-R,core+R,2*radial),
        bins(0,R,radial),
        bins(0,core-R if exact_core else END,4*radial),
    ]
    core_start=0
    core_order=[]
    min_core=-1
    angle_low=angle_high=0
    if phase is not None:
        step=TURN//9
        if TURN%72 or TURN%24 or beta(core,core-R,CORE_CAPS[3])*24>=TURN:
            raise ValueError("insufficient separation for the four core phases")
        core_start=(TURN//18+phase*TURN//36)%step
        min_core=23
        core_order=list(range(14,23))
        core_order.insert(slot+1,min_core)
        angle_low=core_start+slot*step+TURN//24
        angle_high=core_start+(slot+1)*step-TURN//24
        families.append(bins(core-R,CORE_CAPS[3],max(8,radial//2)))
    groups=[(0,1,-1,0)]
    groups.extend((1,0,ring_id[SCALE],(2*i+1)*TURN//26) for i in range(13))
    groups.extend((2,0,ring_id[core],core_start+i*TURN//count) for i in range(count))
    groups.extend([(5 if phase is not None else 2,0,-1,0)]*(core_disks-count))
    groups.append((3,0,-1,0))
    groups.extend([(4,0,-1,0)]*(12-core_disks))
    assert len(groups)==27

    # Each cut is a nonnegative sum of necessary full-circle length bounds.
    cuts=[[(i,1)] for i in range(len(radii))]
    for a,b in ((1000,731),(1000,699),(967,665),(731,538),(699,415),
                (645,490),(625,237),(582,318),(515,255)):
        ia,ib=ring_id[a*10**6],ring_id[b*10**6]
        cuts.extend(([(ia,1),(ib,1)],[(ia,2),(ib,1)]))
    cuts.append([(ring_id[SCALE],1),(ring_id[core],1)])
    counts=[(14,14+core_disks,j,CORE_CAPS[12-core_disks+j])
            for j in range(1,core_disks+1)]
    for j,cap in enumerate(B14_NORM_ORDER,2):
        counts.append((0,14,-(15-j),cap))

    write_data(path,R,angular,rings,families,groups,cuts,counts,OUTER_NORM_UPPER,
               ring_id[core] if exact_core else -1,min_core,angle_low,angle_high,core_order,
               core_disks if exact_core else 0)


def write_data(path,radius,angular,rings,families,groups,cuts,counts,expanded,
               core_ring=-1,min_core=-1,angle_low=0,angle_high=0,core_order=(),exact_core=0):
    with path.open("w",encoding="ascii",newline="\n") as out:
        print("COVER27-POLAR-1",file=out)
        print(TURN,SCALE,radius,angular,len(rings),len(families),len(cuts),file=out)
        for s,samples in rings:
            print(s,samples,file=out)
        for family in families:
            print(len(family),file=out)
            for lo,hi in family:
                print(lo,hi,*(beta(s,lo,hi,radius) for s,_ in rings),file=out)
        for group in groups:
            print(*group,file=out)
        for cut in cuts:
            print(len(cut),*(v for term in cut for v in term),file=out)
        print(len(counts),expanded,file=out)
        for count in counts:
            print(*count,file=out)
        print(core_ring,min_core,angle_low,angle_high,len(core_order),exact_core,file=out)
        if core_order:
            print(*core_order,file=out)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("output",type=Path)
    p.add_argument("--band",type=int,choices=range(len(BANDS)),default=0)
    p.add_argument("--angular",type=int,default=520)
    p.add_argument("--radial",type=int,default=48)
    p.add_argument("--first",type=int,default=0)
    p.add_argument("--last",type=int)
    p.add_argument("--phase",type=int,choices=range(4))
    p.add_argument("--slot",type=int,choices=range(9))
    p.add_argument("--window",nargs=2,type=int,metavar=("LOW","HIGH"))
    p.add_argument("--core-count",type=int)
    a=p.parse_args()
    write_tables(a.output,a.band,a.angular,a.radial,a.first,
                 a.last if a.last is not None else max(3,a.radial//4),a.phase,a.slot,a.window,
                 a.core_count)
