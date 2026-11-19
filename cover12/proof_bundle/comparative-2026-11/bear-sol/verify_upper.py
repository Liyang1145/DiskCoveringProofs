"""Exact fixed-point interval checks for the symmetric covering construction."""

from math import isqrt


class I:
    scale = 10**36

    def __init__(self, x, y=None):
        def grid(v):
            numerator, sep, digits = str(v).partition(".")
            assert len(digits) <= 36
            sign = -1 if numerator.startswith("-") else 1
            return (int(numerator) * self.scale
                    + sign * int(digits or "0") * (self.scale // 10**len(digits)))
        self.a, self.b = grid(x), grid(x if y is None else y)
        assert self.a <= self.b

    @classmethod
    def make(cls, a, b):
        z = cls.__new__(cls)
        z.a, z.b = a, b
        assert a <= b
        return z

    def __neg__(self):
        return I.make(-self.b, -self.a)

    def __add__(self, other):
        y = other if isinstance(other, I) else I(other)
        return I.make(self.a + y.a, self.b + y.b)

    __radd__ = __add__

    def __sub__(self, other):
        return self + -(other if isinstance(other, I) else I(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        y = other if isinstance(other, I) else I(other)
        vals = (self.a*y.a, self.b*y.a, self.a*y.b, self.b*y.b)
        return I.make(min(vals)//self.scale, -(-max(vals)//self.scale))

    __rmul__ = __mul__

    def __truediv__(self, other):
        y = other if isinstance(other, I) else I(other)
        assert y.a*y.b > 0
        vals = [(a*self.scale, b) for a in (self.a,self.b) for b in (y.a,y.b)]
        return I.make(min(a//b for a,b in vals), max(-(-a//b) for a,b in vals))

    def sqrt(self):
        assert self.a >= 0
        a, b = self.a*self.scale, self.b*self.scale
        k = isqrt(b)
        return I.make(isqrt(a), k + (k*k < b))

    def pos(self):
        return self.a > 0

    def __repr__(self):
        def fmt(k):
            return ("-" if k < 0 else "") + str(abs(k)//self.scale) + "." + str(
                abs(k)%self.scale).zfill(36)
        return f"[{fmt(self.a)}, {fmt(self.b)}]"


class J:
    """Value and first and second derivatives in one real variable."""

    def __init__(self, f, d=0, dd=0):
        self.f, self.d, self.dd = (x if isinstance(x, I) else I(x) for x in (f,d,dd))

    def __neg__(self):
        return J(-self.f, -self.d, -self.dd)

    def __add__(self, other):
        y = other if isinstance(other, J) else J(other)
        return J(self.f+y.f, self.d+y.d, self.dd+y.dd)

    __radd__ = __add__

    def __sub__(self, other):
        return self + -(other if isinstance(other, J) else J(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        y = other if isinstance(other, J) else J(other)
        return J(self.f*y.f, self.d*y.f+self.f*y.d,
                 self.dd*y.f+2*self.d*y.d+self.f*y.dd)

    __rmul__ = __mul__

    def __truediv__(self, other):
        y = other if isinstance(other, J) else J(other)
        f = self.f/y.f
        d = (self.d-f*y.d)/y.f
        return J(f, d, (self.dd-2*d*y.d-f*y.dd)/y.f)

    def sqrt(self):
        f = self.f.sqrt()
        d = self.d/(2*f)
        return J(f, d, (self.dd-2*d*d)/(2*f))


def geometry(r, s):
    p = s+r
    x = (1+p)/2
    y = (r*r-(1-x)*(1-x)).sqrt()
    t = s/2+(r*r-3*s*s/4).sqrt()
    b = r+t
    q1 = (x*x-y*y)/(x*x+y*y)
    q2 = 2*x*y/(x*x+y*y)
    return x,y,t,b,q1,q2


def F(r, s):
    _,_,_,b,q1,q2 = geometry(r,s)
    return (q1-b/2)*(q1-b/2)+(q2-b*J(3).sqrt()/2)*(q2-b*J(3).sqrt()/2)-r*r


def vecsub(a,b):
    return [v-w for v,w in zip(a,b)]


def cross(v,w):
    return v[0]*w[1]-v[1]*w[0]


def sq(a):
    return sum(v*v for v in a)


def checks():
    rl,rh = "0.361102963744", "0.361102963745"
    sl,sh = "0.27824163", "0.27824168"
    r,s = I(rl,rh),I(sl,sh)
    s0 = I("0.27824165")
    full = F(J(r),J(s,1))
    assert full.dd.pos()
    assert (-F(J(r),J(sl,1)).d).pos()
    assert F(J(r),J(sh,1)).d.pos()
    assert (-F(J(r,1),J(s)).d).pos()
    shift = full.d*(s-s0)
    assert (F(J(rl),J(s0)).f+shift).pos()
    assert (-F(J(rh),J(s0)).f-shift).pos()

    x,y,t,b,q1,q2 = geometry(r,s)
    sqrt3 = I(3).sqrt()
    assert (I(1)-b).pos() and (t-r).pos() and (r-s).pos() and s.pos()
    assert (x-s).pos() and y.pos() and q2.pos()
    assert (sqrt3*q1-q2).pos() and (2*q1-1).pos()
    assert (s/2).pos() and (b-s/2).pos()

    def rot120(c):
        X,Y = c
        return [(-X-sqrt3*Y)/2,(sqrt3*X-Y)/2]

    a0,a1,b0 = [x,-y],[x,y],[b/2,b*sqrt3/2]
    outer = [a0,a1,b0] + [rot120(c) for c in (a0,a1,b0)]
    outer += [rot120(c) for c in outer[3:6]]
    for k,a in enumerate(outer):
        h = (k+1)%9
        e = vecsub(outer[h],a)
        for j,c in enumerate(outer):
            if j not in (k,h):
                assert cross(e,vecsub(c,a)).pos()

    si = [s,I(0)]
    v,w = vecsub(a1,si),vecsub(b0,si)
    z = cross(v,w)
    assert z.pos()
    assert (4*z*z*r*r - sq(v)*sq(w)*sq(vecsub(v,w))).pos()
    print("PASS: unique root of F=F_s=0 in the stated rectangle")
    print("PASS: all strict geometric tests for the covering construction")
    print(f"Strict upper bound: R < {rh}")


if __name__ == "__main__":
    checks()
