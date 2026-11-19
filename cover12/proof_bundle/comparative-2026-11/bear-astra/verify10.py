"""Rational and integer verification for the ten-boundary-disk cases."""

from argparse import ArgumentParser
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import ctypes
from struct import pack

from verify12 import H, Q, PI, arc_max, arc_units, angle_upper, cmin_edge
from verify_topology12 import (
    M, PIH, TURNL, R, RR, DOPT2, AMAX,
    cos_hi, cos_lo, high, low, q, sqrthi, sqrtlo,
)


def check_ten_radial(data):
    r = Q(data["outer_cutoff"])
    inn = 1-Q(data["r"][0])
    first = data["ten_radial"]["redundant"]
    second = data["ten_radial"]["long_inner"]

    t = Q(first["first"])
    step = Q(first["step"])
    ws = [(t+i*step,w) for i,w in enumerate(first["inner_weights"])]
    ws.append((Q(first["last_exception"]),first["last_exception_weight"]))
    ws.append((Q(1),first["boundary_weight"]))
    t2 = [(Q(t),w) for t,w in second["weighted_circles"]]
    far = Q(second["min_norm"])
    assert far == Q(".525") and far*far < 1-2*r

    for name, m,l,ds,ws,mesh in (
        ("essential exterior arcs",9,2,1-r,ws,first["grid"]),
        ("inner center norms < 0.525",10,1,far,t2,second["grid"]),
    ):
        assert all(type(w) is int and w>0 and 0<t<=1
                   and (t==1 or t*t-r*r<ds*ds) for t,w in ws)
        ao = arc_max(r,ws,1-r,1,mesh)
        ai = arc_max(r,ws,Q(0),inn,mesh)
        ax = sum(w*arc_units(r,t,ds,ds) for t,w in ws if t!=1)
        assert Q(m*ao + l*ai + ax,H) < PI.lo*sum(w for _,w in ws)
        print(f"PASS: ten outer: {name}; arc maxima ({ao}, {ai}, {ax})/{H}",flush=True)


RLO = Q("0.3611029637444")
DMIN = 1-R
DLIM = sqrthi(DOPT2)
TMIN = 1-2*R
BAD = -(2**24)


def unit_arc(d):
    if d*d >= DOPT2:
        return AMAX
    return angle_upper((1+d*d-RR)/(2*d),M)


@lru_cache(maxsize=180000)
def arc_at(r,t,lo,hi):
    if hi<t-r or lo>t+r:
        return 0
    return angle_upper(cmin_edge(r,t,lo,hi),M)


def needed_arcs():
    out = []
    for ts, w in [(".300",117),(".310",94),(".320",80),(".330",70),(".340",61),
                  (".350",54),(".360",49),(".370",44),(".380",40),(".390",36),
                  (".400",32),(".410",28),(".420",26)]:
        t = Q(ts)
        ato = arc_max(R,((Q(1),100),(t,w)),DMIN,Q(1),4000)
        needed = ((PI.lo*(100+w)-Q(10*ato,H))*M/w).__floor__()
        out.append((t,needed))
    return out


def rejected_by_circles(checks,sl,su,pl,pu,gl,gu):
    for t,needed in checks:
        if needed<=0:
            continue
        a,b=arc_at(R,t,sl,su),arc_at(R,t,pl,pu)
        if min(a+b,max(a,b,(a+b+gu+1)//2)) < needed:
            return True
    return False


def side_maxima(sl,su,pl,pu,gl,gu):
    # Use the exact-radius sides: the negative intersection term needs RLO.
    c0,c1 = cos_lo(gu),cos_hi(gl)
    x0,x1 = sl*pl,su*pu
    z0 = max(Q(0),pl-su,sl-pu)**2+2*x0*(1-c1)
    z1 = max(abs(pl-su),abs(sl-pu))**2+2*x1*(1-c0)
    if z0 > 4*RR:
        return None
    tcap=R+min(su,pu)
    if z0 <= 0:
        return tcap,tcap
    # The radial far tips cannot be in the other disk if its line is too
    # far away. This checks the two candidate tips without inferring a side.
    tip_s = max(Q(0),pl-su-R,sl+RLO-pu)**2 + 2*(sl+RLO)*pl*(1-c1)
    tip_p = max(Q(0),sl-pu-R,pl+RLO-su)**2 + 2*(pl+RLO)*sl*(1-c1)
    if min(tip_s,tip_p)<=RR:
        return tcap,tcap
    root_lo= sqrtlo(z0)
    sinhi=sqrthi(1-min(c0*c0,c1*c1)) if c0*c1>0 else Q(1)
    sinlo=sqrtlo(1-max(c0*c0,c1*c1))
    sqmid=RR+max(x0*c1,x1*c1)
    tplus = sqmid+x1*sinhi*sqrthi(max(Q(0),4*RR/z0-1))
    tminus = sqmid-x0*sinlo*sqrtlo(max(Q(0),4*RLO**2/z1-1))
    # The farthest point on the common diameter line is a lens endpoint.
    absx = max(abs(su**2-pl**2),abs(pu**2-sl**2))/(2*root_lo)
    yy = x1*sinhi/root_lo
    axial = (absx+max(Q(0),R-root_lo/2))**2+yy*yy
    up = min(tcap,sqrthi(max(Q(0),axial,tplus)))
    down = min(tcap,sqrthi(max(Q(0),axial,tminus)))
    return up,down


def build_profiles(mesh, cache_size=96, kernel=None):
    import numpy as np

    assert 1 <= mesh <= 1024
    assert 10*(PIH+2) < 2**20
    bounds=[DMIN+(DLIM-DMIN)*Q(i,mesh) for i in range(mesh+1)]
    aa=np.array([unit_arc(d) for d in bounds[1:]],dtype=np.int32)
    direct=aa[:,None]+aa[None,:]

    def plus(a,b):
        if kernel is not None:
            out = np.empty_like(a)
            assert a.dtype == b.dtype == np.dtype("int32")
            assert a.flags.c_contiguous and b.flags.c_contiguous
            kernel(a.ctypes.data,b.ctypes.data,out.ctypes.data,mesh)
            return out
        return (a[:,:,None]+b[None,:,:]).max(axis=1)

    @lru_cache(maxsize=cache_size)
    def profile(sl,su):
        sl,su=max(Q(".05"),q(sl)),min(Q(".525"),q(su))
        ee=np.array([angle_upper(cmin_edge(2*R,d,sl,su),M)
                     for d in bounds[:-1]],dtype=np.int32)
        span=ee[:,None]+ee[None,:]
        rho=R+su

        def inner_beta(d):
            if d*d<=rho*rho+RR:
                return angle_upper(sqrtlo(1-RR/(d*d)),M)
            return angle_upper((d*d+rho*rho-RR)/(2*d*rho),M)

        bb=np.array([inner_beta(d) for d in bounds[:-1]],dtype=np.int32)
        bsum=bb[:,None]+bb[None,:]
        good=np.array([d<=su+2*R for d in bounds[:-1]],dtype=bool)
        allow=good[:,None]&good[None,:]
        e=[]
        for n in range(2):
            cap=np.minimum(direct+2*n*AMAX,bsum)
            e.append((np.where(allow,np.minimum(cap,span),BAD),
                      np.where(allow&(cap+span>=TURNL),cap,BAD)))
        s0=np.full((mesh,mesh),BAD,dtype=np.int32)
        diag=np.where(good,0,BAD)
        np.fill_diagonal(s0,diag)
        s1=np.full_like(s0,BAD)
        vals=[(s0,s1),e[0]]
        for n in range(2,10):
            a,b = e[1] if n==2 else (s1,s1)
            for i,j in product(range(2),repeat=2):
                if i+j+2>n:
                    continue
                p,w=vals[n-i-j-2]
                u,v=e[i]
                x,y=e[j]
                a=np.maximum(a,plus(u,plus(p,x)))
                if np.any(w>=0):
                    b=np.maximum(b,plus(u,plus(w,x)))
                if np.any(v>=0):
                    b=np.maximum(b,plus(v,plus(p,x)))
                if np.any(y>=0):
                    b=np.maximum(b,plus(u,plus(p,y)))
            vals.append((np.where(a>=0,np.minimum(a,span),BAD),
                         np.where(b>=0,b,BAD)))
        return tuple(np.maximum(a,b) for a,b in vals)

    return np,bounds,profile


def check_ten_turns(data,mesh,limit,trace=False,refine=0,kernel=None):
    from bisect import bisect_right

    np, bounds, profile = build_profiles(mesh,kernel=kernel)
    next_profiles = build_profiles(refine,cache_size=80,kernel=kernel) if refine else None
    checks=needed_arcs()
    assert R == Q(data["r"][1]) and RLO == Q(data["r"][0])
    assert Q(".525")**2 < 1-2*R
    low_s, high_s=low(Q(".05")),high(Q(".525"))
    grid=1024
    sectors=[(i,min(i+grid,high_s)) for i in range(low_s,high_s,grid)]
    angles=[(i,min(i+2*grid,PIH)) for i in range(0,PIH,2*grid)]
    stack=[(s,p,g) for s,p in product(sectors,sectors) if s[0]<=p[0] for g in angles]
    done=0
    decisions=sha256()

    def record(b,reason):
        decisions.update(pack("<7i",*b[0],*b[1],*b[2],reason))

    while stack:
        b=stack.pop()
        done+=1
        (sl,su),(pl,pu),(gl,gu)=b
        s0,s1,p0,p1=max(Q(".05"),q(sl)),min(Q(".525"),q(su)),max(Q(".05"),q(pl)),min(Q(".525"),q(pu))
        if s0>p1 or rejected_by_circles(checks,s0,s1,p0,p1,gl,gu):
            record(b,0)
            continue
        rr=side_maxima(s0,s1,p0,p1,gl,gu)
        if rr is None or min(rr)<TMIN:
            record(b,1)
            continue

        def turn_bound(n,bounds,profile):
            i,j=[min(n,bisect_right(bounds,R+t)) for t in rr]
            if i==0 or j==0:
                return BAD
            ps=profile(sl,su)
            qs=profile(pl,pu)
            return max(int(np.max(ps[k][:i,:j]+qs[10-k][:j,:i].T))
                       for k in range(1,10))

        bound=turn_bound(mesh,bounds,profile)
        if bound<TURNL:
            record(b,2)
            continue
        if next_profiles is not None and max(su-sl,pu-pl)<=128 and gu-gl<=512:
            _, nb, npf = next_profiles
            bound=turn_bound(refine,nb,npf)
        if bound<TURNL:
            record(b,3)
            continue
        if trace:
            print("undecided",b,bound,flush=True)
            return False
        if done>=limit:
            raise RuntimeError(("branch budget exceeded",b,bound))
        dim=max((i for i in range(3) if b[i][1]-b[i][0]>=2),
                key=lambda i:(b[i][1]-b[i][0])*(10 if i<2 else 1),default=None)
        if dim is None:
            raise RuntimeError(("unverified turn box",b,bound))
        l,u=b[dim]
        m=(l+u)//2
        record(b,4+dim)
        for sub in ((l,m),(m,u)):
            stack.append(b[:dim]+(sub,)+b[dim+1:])
    digest=decisions.hexdigest()
    cfg=data["ten_turns"]
    if [mesh,refine]==cfg["mesh"]:
        assert done==cfg["boxes"] and digest==cfg["sha256"]
    print(f"PASS: ten outer: two-run angle budget; checked boxes={done},"
          f" mesh={mesh}, refinement={refine}",flush=True)
    print(f"PASS: ten outer: decision SHA-256 {digest}",flush=True)
    return True


def check_kernel(func):
    import numpy as np

    for n in (5,19):
        ij = np.arange(n*n,dtype=np.int32).reshape(n,n)
        a = np.where(ij%3==0,BAD,(119*ij+37)%138547)
        b = np.ascontiguousarray(np.where(ij%7==0,BAD,(331*ij+9)%91121).T)
        result = np.empty_like(a)
        func(a.ctypes.data,b.ctypes.data,result.ctypes.data,n)
        expected=np.maximum(BAD,(a[:,:,None]+b[None,:,:]).max(axis=1))
        expected=np.where(expected<0,BAD,expected)
        assert np.array_equal(result,expected)


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O.")
    p=ArgumentParser()
    p.add_argument("--turns",action="store_true")
    p.add_argument("--mesh",type=int)
    p.add_argument("--refine",type=int)
    p.add_argument("--limit",type=int)
    p.add_argument("--trace",action="store_true")
    p.add_argument("--native",action="store_true")
    args=p.parse_args()
    data = json.loads(Path("certificate12.json").read_text(encoding="ascii"))
    if args.turns:
        k = None
        if args.native:
            lib = ctypes.CDLL(str(Path("turn_kernel12.dll").resolve()))
            k = lib.turn_maxplus
            k.argtypes = [ctypes.c_void_p]*3+[ctypes.c_int]
            k.restype = None
            check_kernel(k)
        c=data["ten_turns"]
        mesh = c["mesh"][0] if args.mesh is None else args.mesh
        refine = c["mesh"][1] if args.refine is None else args.refine
        limit = c["max_boxes"] if args.limit is None else args.limit
        assert limit > 0 and 1 <= mesh <= 1024 and 0 <= refine <= 1024
        if not check_ten_turns(data,mesh,limit,args.trace,refine,k):
            raise SystemExit(2)
    else:
        check_ten_radial(data)
