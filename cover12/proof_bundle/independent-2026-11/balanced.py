"""Fixed-point interval certificate for the balanced-chain angle inequality."""
from fractions import Fraction
from math import acos, factorial, floor, isqrt
from exact_angles import PI_LO, PI_HI, SCALE, TURN, check_constants

S = 10**25


class Iv:
    def __init__(self, a, b=None, *, raw=False):
        if raw:
            self.lo, self.hi = a, b
        else:
            a, b = Fraction(a), Fraction(a if b is None else b)
            self.lo = (a.numerator*S)//a.denominator
            self.hi = -((-b.numerator*S)//b.denominator)
        assert self.lo <= self.hi

    def __neg__(self):
        return Iv(-self.hi, -self.lo, raw=True)

    def __add__(self, other):
        x = wrap(other)
        return Iv(self.lo+x.lo, self.hi+x.hi, raw=True)

    __radd__ = __add__

    def __sub__(self, other):
        return self+-wrap(other)

    def __rsub__(self, other):
        return wrap(other)+-self

    def __mul__(self, other):
        x = wrap(other)
        p = (self.lo*x.lo, self.lo*x.hi, self.hi*x.lo, self.hi*x.hi)
        return Iv(min(p)//S, -((-max(p))//S), raw=True)

    __rmul__ = __mul__

    def __truediv__(self, other):
        x = wrap(other)
        assert x.lo*x.hi > 0
        return self*Iv(S*S//x.hi, -((-S*S)//x.lo), raw=True)

    def sq(self):
        p, q = self.lo*self.lo, self.hi*self.hi
        a = 0 if self.lo<=0<=self.hi else min(p,q)//S
        return Iv(a, -((-max(p,q))//S), raw=True)

    def sqrt(self):
        assert self.lo >= 0
        return Iv(isqrt(self.lo*S), isqrt(self.hi*S)+1, raw=True)

    def mag(self):
        return max(abs(self.lo),abs(self.hi))

    def mid(self):
        t = (self.lo+self.hi)//2
        return Iv(t,t,raw=True)

    def point(self, upper):
        t=self.hi if upper else self.lo
        return Iv(t,t,raw=True)


def wrap(x):
    return x if isinstance(x,Iv) else Iv(x)


COS = [Iv(Fraction((-1)**j, factorial(2*j))) for j in range(12, -1, -1)]
REM = Iv(Fraction(1, factorial(26)))
PI = Iv(PI_LO, PI_HI)
R = Iv("0.36110296374450864411","0.36110296374450864412")
U = Iv("0.27824166087","0.27824166088")
D0 = 2*PI/3

def cos_point(x):
    """Cosine enclosure from degree 24 and degree 26 Taylor bounds."""
    v = COS[0]
    x2 = x.sq()
    for c in COS[1:]:
        v = v*x2+c
    rem = REM
    for _ in range(13):
        rem=rem*x2
    return Iv(v.lo-rem.hi,v.hi,raw=True)


def cos_range(x):
    assert 0 <= x.lo <= x.hi <= PI.lo
    return Iv(cos_point(x.point(True)).lo, cos_point(x.point(False)).hi, raw=True)


def acos_point(g):
    assert -S < g < S
    tick = 10**12
    nominal = int(acos(g/S)*tick)
    lo,hi = nominal-2,nominal+2
    while cos_point(Iv(Fraction(lo,tick))).lo<g:
        lo-=2
    while cos_point(Iv(Fraction(hi,tick))).hi>g:
        hi+=2
    assert 0<=lo<=hi and Fraction(hi,tick)<PI_LO
    return Iv(Fraction(lo,tick),Fraction(hi,tick))


def alpha(t):
    g = (1+t.sq()-R.sq())/(2*t)
    return Iv(acos_point(g.hi).lo,acos_point(g.lo).hi,raw=True)


def alpha_derivatives(t, second=False):
    g = (1+t.sq()-R.sq())/(2*t)
    z = (1-g.sq()).sqrt()
    gp = (1-(1-R.sq())/t.sq())/2
    a1 = -gp/z
    if not second:
        return a1
    gpp = (1-R.sq())/(t.sq()*t)
    return a1, -gpp/z - g*gp.sq()/(z.sq()*z)


def lens(w,d=None):
    c = Iv("0.5") if d is None else cos_range(d/2)
    s = (1-c.sq()).sqrt()
    z = (R.sq()-w.sq()*s.sq()).sqrt()
    h = w*c+z
    return h, s, c, z


def lens_first(w,s,c,z):
    return c-w*s.sq()/z, -w*s/2-w.sq()*s*c/(2*z)


def H(w):
    return 2*alpha((w+R+R.sq()).sqrt())


def derivs(w,d,second=False):
    h,s,c,z=lens(w,d)
    hw,hd=lens_first(w,s,c,z)
    t=(w+R+R.sq()).sqrt()
    v=R+h
    if not second:
        a1=alpha_derivatives(v)
        return alpha_derivatives(t)/t+a1*hw,a1*hd
    a1,a2=alpha_derivatives(v,True)
    b1,b2=alpha_derivatives(t,True)
    hww=-s.sq()/z-w.sq()*s.sq().sq()/(z.sq()*z)
    hwd=-s/2-w*s*c/z-w.sq()*w*s.sq()*s*c/(2*z.sq()*z)
    hdd=-w*c/4-w.sq()*(c.sq()-s.sq())/(4*z)-w.sq().sq()*s.sq()*c.sq()/(4*z.sq()*z)
    kww=b2/(2*t.sq())-b1/(2*t.sq()*t)+a2*hw.sq()+a1*hww
    kwd=a2*hw*hd+a1*hwd
    kdd=a2*hd.sq()+a1*hdd
    return kww, kww*kdd-kwd.sq()


def split(w,d):
    if (w.hi-w.lo)*4>d.hi-d.lo:
        t=w.mid().lo
        return [(Iv(w.lo,t,raw=True),d),(Iv(t,w.hi,raw=True),d)]
    t=d.mid().lo
    return [(w,Iv(d.lo,t,raw=True)),(w,Iv(t,d.hi,raw=True))]


def certify_rectangle(initial, check):
    queue=list(initial)
    visited=0
    while queue:
        w,d=queue.pop()
        visited+=1
        try:
            passed=check(w,d)
        except AssertionError:
            passed=False
        if passed:
            continue
        assert min(w.hi-w.lo,d.hi-d.lo)>S//10**8
        queue.extend(split(w,d))
    return visited


def verify():
    check_constants()
    h,s,c,z=lens(U)
    lam=alpha_derivatives(R+h)*lens_first(U,s,c,z)[1]
    assert lam.hi<0
    widths=[Iv(".10",".263"),Iv(".263",".293"),Iv(".293",".37")]
    gaps=[Iv("1.40","2.025"),Iv("2.025","2.165"),Iv("2.165","2.35")]
    assert widths[1].lo < U.lo < U.hi < widths[1].hi
    assert gaps[1].lo < D0.lo < D0.hi < gaps[1].hi

    def hessian(w,d):
        x,det=derivs(w,d,True)
        return x.hi<0 and det.lo>0

    n_hessian=certify_rectangle([(widths[1],gaps[1])],hessian)
    assert (H(Iv(".37"))+alpha(2*R)-PI/3-lam*(Iv("2.35")-D0)).hi < 0

    def tangent(w,d):
        h,*_=lens(w,d)
        if h.hi<=R.lo:
            return True
        wm,dm=w.mid(),d.mid()
        v=R+lens(wm,dm)[0]
        q=H(wm)+alpha(v)-PI/3-lam*(dm-D0)
        if q.hi>=0:
            return False
        qw,qd=derivs(w,d)
        bw=(w.hi-w.lo+1)//2
        bd=(d.hi-d.lo+1)//2
        return q.hi-((-qw.mag()*bw)//S)-((-(qd-lam).mag()*bd)//S)<0

    outer=[(w,d) for i,w in enumerate(widths) for j,d in enumerate(gaps) if (i,j)!=(1,1)]
    n_tangent=certify_rectangle(outer,tangent)

    def line(d):
        return PI/3+lam*(d-D0)

    opt=(1-R.sq()).sqrt()
    max_arc=alpha(opt)

    def arc_cap(z):
        u=z.point(True)
        if u.lo>=opt.lo:
            return max_arc
        if u.lo<=S-R.hi:
            return Iv(0)
        g=((1+u.sq()-R.sq())/(2*u)).lo
        if g>=S:
            return Iv(0)
        assert g>-S
        k=10**12
        hi=int(acos(g/S)*k)+2
        while cos_point(Iv(Fraction(hi,k))).hi>g:
            hi+=2
        return Iv(0,Fraction(hi,k))

    # For d <= 1.4, 3 asin(r) is already below the tangent line.
    assert (3*max_arc-line(Iv("1.4"))).hi < 0
    c=cos_point(Iv(".8"))
    assert (R*c/(1-c.sq()).sqrt()).hi < Iv(".37").lo

    # For w >= .37, cap the high-pair term at 2 asin(r). On the
    # second interval h(w,d) is decreasing in w.
    def large_average(d,use_lens):
        if use_lens:
            h=lens(Iv(".37"),d.point(False))[0]
        else:
            c=cos_range(d.point(False)/2)
            h=R/(1-c.sq()).sqrt()
        upper=Iv(max(R.lo,h.lo),max(R.hi,h.hi),raw=True)
        return (2*max_arc+arc_cap(R+upper)-line(d)).hi<0

    def angle_interval(d,use_lens):
        todo=[d]
        visited=0
        while todo:
            sub=todo.pop()
            visited+=1
            if large_average(sub,use_lens):
                continue
            assert sub.hi-sub.lo > S//10**8
            t=sub.mid().lo
            todo.extend([Iv(sub.lo,t,raw=True),Iv(t,sub.hi,raw=True)])
        return visited

    n_large=angle_interval(Iv("1.4","1.6"),False)+angle_interval(Iv("1.6","2.35"),True)

    # For d >= 2.35 use the exact formula for the radius of the far
    # intersection. If both inner radii are at least a, uv >= 2wa-a^2.
    def obtuse(w,d,a):
        c=cos_range(d.point(False)/2)
        s=(1-c.sq()).sqrt()
        ww=w.point(False)
        delta=R.sq()/(ww.sq()*s.sq())-1
        if delta.hi<0:
            return True
        root=Iv(max(delta.lo,0),delta.hi,raw=True).sqrt()
        coeff=2*c.sq()-1+2*s*c*root
        coefficient=coeff.point(True)
        product=w.point(True).sq() if coefficient.hi>=0 else 2*ww*a-a.sq()
        norm2=R.sq()+product*coefficient
        if norm2.hi<0:
            return True
        h=Iv(0,norm2.hi,raw=True).sqrt()
        cap=2*arc_cap((w+R+R.sq()).sqrt())+arc_cap(R+h)
        return (cap-line(d)).hi<0

    c=cos_point(Iv("1.175"))
    assert (R/(1-c.sq()).sqrt()).hi < Iv(".394").lo
    n_obtuse=certify_rectangle([(Iv(".10",".394"),Iv("2.35","2.65"))],
                               lambda w,d:obtuse(w,d,Iv(".10")))
    n_obtuse+=certify_rectangle([(Iv(".14",".394"),Iv("2.35",PI_HI))],
                                lambda w,d:obtuse(w,d,Iv(".14")))
    # Angular tick and cosine bounds used by the exact C++ recognizer.
    assert 425134683 == floor(Fraction("2.65")*TURN/(2*PI_HI))
    assert cos_point(Iv("2.65")).hi <= Iv(Fraction(-881582193,SCALE)).lo
    r=Fraction(".361102964")
    sin_low=Fraction(".7")-Fraction(".7")**3/6
    assert (r*(1+1/sin_low))**2 < 1-r*r
    assert Fraction(".37")+r+r*r<1-r*r
    print("Balanced-chain inequality verified:",n_hessian,"Hessian boxes and",
          n_tangent+n_large+n_obtuse,"supporting-plane boxes.")


if __name__=="__main__":
    verify()
