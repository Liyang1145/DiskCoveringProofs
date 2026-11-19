"""Global two-variable inequality for nine boundary disks."""

from math import factorial

from verify_local import acos_derivatives, inner, outer
from verify_nine_structure import pt
from verify_upper import I, J, geometry

R = I("0.361102963744","0.361102963745")
S0 = I("0.27824163","0.27824168")


def atan_small(x):
    assert -I("0.415").a <= x.a <= x.b <= I("0.415").a
    w = -x*x
    p, q = x, x
    for k in range(1,24):
        p = p*w
        q = q+p/(2*k+1)
    return q+I("-0.00000000000000000001","0.00000000000000000001")


def acos_pt(u):
    if u >= I.scale:
        return I(0)
    if u <= -I.scale:
        return I("3.14159265358979323845","3.14159265358979323848")
    if u < 0:
        return acos_pt(-I.scale)-acos_pt(-u)
    z = ((I.scale-u)*I.scale//(I.scale+u),
         -(-((I.scale-u)*I.scale)//(I.scale+u)))
    v = I.make(*z).sqrt()
    return 4*atan_small(v/(1+(1+v*v).sqrt()))


def acos(v):
    return I.make(acos_pt(v.b).a,acos_pt(v.a).b)


def min_i(u,v):
    return I.make(min(u.a,v.a),min(u.b,v.b))


def alpha_j(r,s):
    x = (1+s+r)/2
    y = (r*r-(1-x)*(1-x)).sqrt()
    sq = x.f*x.f+y.f*y.f
    d = (x.f*y.d-y.f*x.d)/sq
    dd = (x.f*y.dd-y.f*x.dd-2*d*(x.f*x.d+y.f*y.d))/sq
    return J(0,d,dd)


def controls():
    # Check pi bracket in acos_pt, and Taylor arctangent error at 0.415.
    plo,phi = "3.14159265358979323845","3.14159265358979323848"
    # Longer series at the two tightly spaced endpoints; rigorous error.
    err = I("0.00000000000000000000000000000000001")
    assert 4**72 * I.scale < err.a * factorial(72)
    for p, sign in ((plo,1),(phi,-1)):
        x = I(p)
        w, a, z = -x*x,x,x
        for k in range(1,36):
            a = a*w/((2*k)*(2*k+1))
            z = z+a
        assert (sign*z-err).pos()
    assert 415**49*10**20 < 49*1000**49

    r = R
    sr = 1-2*r*r-r
    assert sr.a > I("0.14").a
    qos = I("0.001").a
    for k in range(I("0.14").a,sr.b,qos):
        s = I.make(k,min(k+qos,sr.b))
        x,y,_,_,_,_ = geometry(r,s)
        d = (x*x+y*y).sqrt()
        nu_x,nu_y = (1-x)/r,y/r
        # nu is in (A,pi/2), hence in (v,pi/2) for any feasible arc.
        assert (nu_y-r).pos() and nu_x.pos()
        # At the tangent's anchor, the supporting point is the inner vertex.
        assert (y/d-r*(nu_y*x/d-nu_x*y/d)).pos()
        al = acos(x/d)
        ap = alpha_j(J(r),J(s,1)).d
        assert (nu_x*al-ap*(2*r-nu_x*(1-r-s))).pos()
    assert (1-2*r*r-2*r).pos()
    print("PASS: global high-pair supporting inequality for |S| >= 0.14")
    return sr


def evaluate(r,t,s,sr,a):
    # Angular values; formulas use saturation at the geometric maxima.
    z = min_i(s,sr)
    x = (1+z+r)/2
    sq = z+r+r*r
    al = acos(x/sq.sqrt())
    d = min_i(t+r,(1-r*r).sqrt())
    be = acos((1+d*d-r*r)/(2*d))
    ga = acos((t*t+s*s-r*r)/(2*t*s))
    return be/2+a*ga+al


def smooth(r,t,s,sr):
    z = (t*t+s*s-r*r)/(2*t*s)
    d = t+r
    w = (1+d*d-r*r)/(2*d)
    return (-I.scale < z.a <= z.b < I.scale and s.b < sr.a
            and d.b < (1-r*r).sqrt().a and -I.scale < w.a <= w.b < I.scale)


def derivatives(r,t,s,a):
    br = outer(J(r),J(t,1))
    yt = inner(J(r),J(t,1),J(s))
    ys = inner(J(r),J(t),J(s,1))
    zz = alpha_j(J(r),J(s,1))
    return (br.d/2+a*yt.d, a*ys.d+zz.d, br.dd/2+a*yt.dd, a*ys.dd+zz.dd)


def hessian(r,t,s,a):
    _,_,tt,ss = derivatives(r,t,s,a)
    jt = inner(J(r),J(t,1),J(s))
    js = inner(J(r),J(t),J(s,1))
    jd = inner(J(r),J(t,1),J(s,1))
    ts = a*(jd.dd-jt.dd-js.dd)/2
    return (-tt).pos() and (-ss).pos() and (tt*ss-ts*ts).pos()


def mid(x):
    return pt((x.a+x.b)//2)


def split(x):
    m = mid(x).a
    assert x.a < m < x.b
    return I.make(x.a,m),I.make(m,x.b)


def tiles(x,step):
    return [I.make(k,min(k+step,x.b)) for k in range(x.a,x.b,step)]


def proof():
    sr = controls()
    r,s = R,S0
    t = geometry(r,s)[2]
    a = -outer(J(r),J(t,1)).d/(2*inner(J(r),J(t,1),J(s)).d)
    assert a.pos()
    # At the true root cos(gamma)=1/2 and 2*alpha+beta=pi/3.
    # The potential's reference value is exactly pi*(1+2*a)/6.
    ref = acos_pt(-I.scale)*(1+2*a)/6
    local_t,local_s = I("0.401","0.415"),I("0.263","0.295")
    assert local_t.a<t.a<=t.b<local_t.b and local_s.a<s.a<=s.b<local_s.b
    for u in tiles(local_t,I("0.00025").a):
        for v in tiles(local_s,I("0.00025").a):
            assert smooth(r,u,v,sr)
            assert hessian(r,u,v,a)
    print("PASS: negative definite Hessian throughout the reference rectangle",flush=True)

    def below(t,s):
        if (ref-evaluate(r,t,s,sr,a)).pos():
            return True
        if smooth(r,t,s,sr):
            tm,sm = mid(t),mid(s)
            ft,fs,_,_ = derivatives(r,t,s,a)
            v = evaluate(r,tm,sm,sr,a)+ft*(t-tm)+fs*(s-sm)
            return (ref-v).pos()
        return False

    def exclude(t,s):
        todo = [(t,s)]
        count = 0
        while todo:
            t,s = todo.pop()
            count += 1
            assert count < 400000
            if below(t,s):
                continue
            assert max(t.b-t.a,s.b-s.a)>I("0.000001").a, (t,s)
            if t.b-t.a >= s.b-s.a:
                todo.extend((l,s) for l in split(t))
            else:
                todo.extend((t,l) for l in split(s))
        return count

    it,iss = I("0.30","1"),I("0.14","1")
    total = exclude(I.make(it.a,local_t.a),iss)
    total += exclude(I.make(local_t.b,it.b),iss)
    total += exclude(local_t,I.make(iss.a,local_s.a))
    total += exclude(local_t,I.make(local_s.b,iss.b))
    print(f"PASS: global potential exclusion outside the reference rectangle ({total} boxes)")


if __name__ == "__main__":
    proof()
