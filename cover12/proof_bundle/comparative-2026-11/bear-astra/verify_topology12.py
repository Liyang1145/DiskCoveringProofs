"""Rational box checks for contact patterns of nine boundary disks."""

from argparse import ArgumentParser
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

from verify12 import PI, Q, angle_upper, cos_upper, I, cmin_edge


M = 2**15
ONE = Q(1)
PIL = (PI.lo*M).__floor__()
PIH = (PI.hi*M).__ceil__()
TURNL = (2*PI.lo*M).__floor__()
TURNH = (2*PI.hi*M).__ceil__()
R = Q("0.3611029637446")
RR = R*R
DOPT2 = 1-RR
SLO = (Q("0.1")*M).__floor__()
SHI = (Q("0.639")*M).__ceil__()
TMIN = Q("0.311")


def low(x):
    return (x*M).__floor__()


def high(x):
    return (x*M).__ceil__()


@lru_cache(maxsize=None)
def q(i):
    return Q(i, M)


@lru_cache(maxsize=None)
def sqrtlo(x):
    return I(x).sqrt().lo


@lru_cache(maxsize=None)
def sqrthi(x):
    return I(x).sqrt().hi


@lru_cache(maxsize=None)
def cos_hi(i):
    assert 0 <= i <= PIH
    if i >= PIH:
        return Q(-1) + Q(1, M)
    return min(ONE, cos_upper(i, M))


@lru_cache(maxsize=None)
def cos_lo(i):
    if i >= PIH:
        return Q(-1)
    x = q(i)
    v = Q(1)
    for j in range(1, 12):
        v *= -x*x/(2*j*(2*j-1))
    return max(Q(-1), cos_upper(i,M)+v)


def ac(c):
    return min(PIH, angle_upper(c, M))


AMAX = ac(sqrtlo(DOPT2))


@lru_cache(maxsize=None)
def alpha_upper(i):
    d = q(i)
    if d*d >= DOPT2:
        return AMAX
    return ac((1+d*d-RR)/(2*d))


@lru_cache(maxsize=None)
def h_upper(j):
    b2 = RR+R+q(j)
    if b2 >= DOPT2:
        return AMAX
    return ac((1+R+q(j))/(2*sqrthi(b2)))


@lru_cache(maxsize=None)
def alpha_to_d_lower(i):
    if i <= 0:
        return low(R+TMIN)
    c = cos_hi(i)
    z = RR+c*c-1
    if z < 0:
        return high(ONE)
    return max(low(R+TMIN), low(c-sqrthi(z)))


def d_interval_gap(lo, hi, lo2, hi2):
    return max(0, lo-hi2, lo2-hi)


@lru_cache(maxsize=250000)
def lens_upper(sl, su, pl, pu, gl):
    if (sl, su) > (pl, pu):
        return lens_upper(pl, pu, sl, su, gl)
    s0, s1, p0, p1 = q(sl), q(su), q(pl), q(pu)
    s0 = max(s0,Q("0.1"))
    p0 = max(p0,Q("0.1"))
    c = cos_hi(gl)
    ddlo = d_interval_gap(s0,s1,p0,p1)**2+2*s0*p0*(1-c)
    if ddlo > 4*RR:
        return 0
    tip1 = d_interval_gap(s0+R,s1+R,p0,p1)**2+2*(s0+R)*p0*(1-c)
    tip2 = d_interval_gap(s0,s1,p0+R,p1+R)**2+2*s0*(p0+R)*(1-c)
    t = R+min(s1,p1)
    if tip1 > RR and tip2 > RR:
        u = RR+max(s0*p0*c, s1*p1*c)
        u += sqrthi((4*RR-ddlo)*s1*p1*(1+c)/2)
        if u < 0:
            return 0
        t = min(t, sqrthi(u))
    return high(R+t)


@lru_cache(maxsize=250000)
def contact_cap(sl, su, d):
    c = cmin_edge(2*R, q(d), max(q(sl),Q("0.1")), q(su))
    return ac(c)


def contact_dirs(s, p, g, dl):
    e, f = contact_cap(*s,dl), contact_cap(*p,dl)
    gl, gu = g
    intervals = []
    for l, u in ((-TURNH,-TURNL), (0,0), (TURNL,TURNH)):
        a = max(-e, gl+l-f)
        b = min(e, gu+u+f)
        if a <= b:
            intervals.append((a,b))
    return intervals


def group_upper(k, sl, su):
    return 2*(k//2)*h_upper(su)+(k%2)*AMAX


def run_impossible(s, g, i, k, a, need, run_hi, turn_lo):
    j = (i-1)%3
    x = (-g[j][1],-g[j][0])
    y = g[i]
    amin, amax = max(0,need-a[j]), a[i]
    bmin, bmax = max(0,need-a[i]), a[j]

    def excludes(al, au, bl, bu):
        if al > au or bl > bu:
            return True
        lo_a = alpha_to_d_lower(al)
        lo_b = alpha_to_d_lower(bl)
        left = contact_dirs(s[i],s[j],x,lo_b)
        right = contact_dirs(s[i],s[(i+1)%3],y,lo_a)
        turn_hi = au+bu+2*run_hi
        return all(yh-xl < turn_lo or yl-xh > turn_hi
                   for (xl,xh),(yl,yh) in product(left,right))

    if excludes(amin,amax,bmin,bmax):
        return True
    if k>1 or amax-amin < 1:
        return False
    pieces = 4
    for p in range(pieces):
        al = amin+(amax-amin)*p//pieces
        au = amin+(amax-amin)*(p+1)//pieces
        if not excludes(al,au,max(bmin,need-au),bmax):
            return False
    return True


def test_triangle(box, k):
    s = box[:3]
    (gl,gu), (pl,pu) = box[3:]
    g = ((gl,gu),(pl,pu),
         (max(0,TURNL-gu-pu), min(PIH,TURNH-gl-pl)))
    if g[2][0] > g[2][1]:
        return True
    # The exterior circle sees each low disk once, so each contributes its
    # own half-angle; the other disks can be paired within each run.
    b = [group_upper(z,*x) for z,x in zip(k,s)]
    groups = sum(b)
    d = [lens_upper(*s[i],*s[(i+1)%3],g[i][0]) for i in range(3)]
    if any(q(x) < R+TMIN for x in d):
        return True
    a = [alpha_upper(x) for x in d]
    total = groups + sum(a)
    if total < PIL:
        return True
    u = [a[i-1]+a[i]+2*b[i] for i in range(3)]
    for i in range(3):
        if run_impossible(s,g,i,k[i],a,PIL-groups-a[(i+1)%3],
                          b[i],max(0,TURNL-u[i-1]-u[(i+1)%3])):
            return True
    return False


def check_triangle(groups,max_boxes):
    box = ((SLO,SHI),)*3 + ((0,PIH),)*2
    stack = [box]
    done = 0
    while stack:
        b = stack.pop()
        done += 1
        if done > max_boxes:
            raise RuntimeError(("branch budget exceeded", groups, b))
        if test_triangle(b,groups):
            continue
        i = max((i for i in range(len(b)) if b[i][1]-b[i][0]>=2),
                key=lambda i:(b[i][1]-b[i][0])*(4 if i<3 else 1), default=None)
        if i is None:
            raise RuntimeError(("unverified contact box",groups,b))
        l,u = b[i]
        m = (l+u)//2
        if m <= l:
            raise RuntimeError(("unverified contact box",groups,b))
        stack.extend(b[:i]+(piece,)+b[i+1:] for piece in ((l,m),(m,u)))
    print(f"PASS: triangle groups={groups}, checked boxes={done}",flush=True)


def discrete_boxes(box, test, label, limit, scales):
    stack = [box]
    n = 0
    while stack:
        b = stack.pop()
        n += 1
        if test(b):
            continue
        if n >= limit:
            raise RuntimeError(("branch budget exceeded",label,b))
        i = max((i for i,(lo,hi) in enumerate(b) if hi-lo>=2),
                key=lambda i: scales[i]*(b[i][1]-b[i][0]), default=None)
        if i is None:
            raise RuntimeError(("unverified box",label,b))
        lo,hi = b[i]
        m = (lo+hi)//2
        for sub in ((lo,m),(m,hi)):
            stack.append(b[:i]+(sub,)+b[i+1:])
    print(f"PASS: {label}, checked boxes={n}",flush=True)


def check_structural(data, limit):
    rlo = Q(data["r"][0])
    dmin = q(low(R+TMIN))
    assert dmin < rlo+TMIN
    assert Q("0.639") < 2*rlo and dmin*dmin < 4*RR
    assert cos_hi(low(Q("2.06"))) < (Q(".01")+dmin*dmin-4*RR)/(Q(".2")*dmin)
    assert cos_hi(low(Q("0.58")))**2 < 1-(R/dmin)**2
    assert Q("2.06")+Q("0.58") < PI.lo
    assert 2*Q("2.06")+2*q(AMAX) < 2*PI.lo
    assert Q("2.16")+2*Q("2.06") < 2*PI.lo
    assert Q("2.16")>PI.hi/2
    assert 2*alpha_upper(high(2*R))+7*AMAX < PIL
    assert TMIN > R-Q("0.1") and dmin > 2*R-Q("0.1")
    small = ac((Q(".01")+TMIN*TMIN-RR)/(Q(".2")*TMIN))
    assert 2*q(small)+PI.hi < 2*PI.lo + PI.lo/2
    assert 2*q(small) < 2*PI.lo-Q("2.16")

    def long(b):
        s,p,d,e = b
        uv = max(q(s[0]),Q(".1"))*max(q(p[0]),Q(".1"))
        if uv > RR-TMIN*TMIN:
            return True
        aa = alpha_upper(high(R+sqrthi(RR-uv)))
        al,bl = alpha_upper(d[1]),alpha_upper(e[1])
        if al+bl+aa+6*AMAX < PIL:
            return True
        if q(d[0]) > q(s[1])+2*R or q(e[0]) > q(p[1])+2*R:
            return True
        if (contact_cap(*s,d[0])+contact_cap(*p,e[0])+2*aa+al+bl) < PIL:
            return True
        return False

    dbox = (low(R+TMIN), high(sqrthi(DOPT2)))
    discrete_boxes(((SLO,SHI),)*2+(dbox,)*2, long, "large single transition",
                   limit, (2,2,3,3))

    def two(b, sign):
        s,p,g = b
        sl, su = max(Q(".1"),q(s[0])),q(s[1])
        pl, pu = max(Q(".1"),q(p[0])),q(p[1])
        c0,c1 = cos_lo(g[1]),cos_hi(g[0])
        c1 = min(Q(0),c1)
        x0,x1 = sl*pl,su*pu
        z0 = d_interval_gap(sl,su,pl,pu)**2+2*x0*(1-c1)
        z1 = max(abs(sl-pu),abs(su-pl))**2+2*x1*(1-c0)
        if z0 > 4*RR:
            return True
        assert z0>0
        v0 = sqrtlo(max(Q(0),1-c0*c0))
        v1 = sqrthi(1-c1*c1)

        def lens2(rhi,rlo,k):
            if k==1:
                shift = x1*v1*sqrthi(max(Q(0),4*rhi*rhi/z0-1))
            else:
                shift = -x0*v0*sqrtlo(max(Q(0),4*rlo*rlo/z1-1))
            return rhi*rhi+x0*c1+shift

        csq = lens2(2*R,2*rlo,sign)
        tsq = lens2(R,rlo,-sign)
        if csq < dmin*dmin or tsq < TMIN*TMIN:
            return True
        a = alpha_upper(high(sqrthi(csq)))
        c = alpha_upper(high(R+sqrthi(tsq)))
        return a+c+7*AMAX < PIL

    for sign in (-1,1):
        discrete_boxes(((SLO,SHI),)*2+((low(Q("2.16")),PIH),),
                       lambda b:two(b,sign),f"merged transition branch {sign}",
                       limit,(4,4,1))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O.")
    p = ArgumentParser()
    p.add_argument("--groups",nargs=3,type=int)
    p.add_argument("--limit",type=int,default=500000)
    p.add_argument("--structural",action="store_true")
    a = p.parse_args()
    cfg = json.loads(Path("certificate12.json").read_text(encoding="ascii"))
    assert R == Q(cfg["r"][1]) and R+TMIN < 1
    assert 1-Q(cfg["r"][0]) < Q("0.639")
    assert low(Q(cfg["r"][0])+TMIN) == low(R+TMIN)
    if a.structural:
        check_structural(cfg, a.limit)
        raise SystemExit()
    k_list = [tuple(a.groups)] if a.groups else [
        (1,2,3), (1,1,4), (0,3,3), (0,2,4), (0,1,5), (0,0,6)]
    for groups in k_list:
        check_triangle(groups,a.limit)
