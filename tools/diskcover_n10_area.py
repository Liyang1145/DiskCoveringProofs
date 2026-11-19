# SPDX-License-Identifier: MIT
"""Directed arithmetic for Fejes Tóth's n=10 area bounds, not a geometry replay.

Primary source: https://library.slmath.org/books/Book52/files/18fejes.pdf
(pages 363, 366–368, 373–375). Every endpoint is an exact rational;
rounding after operations is outward on a 10**24 grid. The pentagon extremum,
area partition, and combinatorial exclusions belong to the accompanying written proof.
"""
from fractions import Fraction as F
from math import factorial, isqrt

S = 10**24

def _out(a, b):
    return F(a*S//1,S), F(-((-b*S)//1),S)

class I:
    def __init__(self, a, b=None):
        self.a, self.b = _out(F(a), F(a if b is None else b))

    def __add__(self, q):
        q = _i(q)
        return I(self.a+q.a, self.b+q.b)
    __radd__ = __add__

    def __neg__(self):
        return I(-self.b, -self.a)

    def __sub__(self, q):
        return self + -_i(q)

    def __rsub__(self, q):
        return _i(q) + -self

    def __mul__(self, q):
        q = _i(q)
        p = [a*b for a in (self.a,self.b) for b in (q.a,q.b)]
        return I(min(p),max(p))
    __rmul__ = __mul__

    def __truediv__(self, q):
        q = _i(q)
        if q.a <= 0 <= q.b:
            raise ArithmeticError("division interval includes zero")
        return self * I(1/q.b, 1/q.a)

def _i(x):
    return x if isinstance(x,I) else I(x)

def _sqrt(x):
    if x.a < 0:
        raise ArithmeticError("negative square root interval")
    lo = isqrt((x.a*S*S)//1)
    hi = isqrt((x.b*S*S)//1)
    if F(hi*hi,S*S) < x.b:
        hi += 1
    return I(F(lo,S),F(hi,S))

def _trig_point(x, parity):
    # At x in [0,2], terms from the final retained term on decrease.
    if not 0 <= x <= 2:
        raise ArithmeticError("unsupported trigonometric argument")
    s = sum((-1)**j*x**(2*j+parity)/factorial(2*j+parity)
            for j in range(22))
    e = x**(44+parity)/factorial(44+parity)
    return I(s,s+e)

def _sin(x):
    # Only subintervals of [0,pi/2) are used; 3/2 is a safe rational cap.
    if not 0 <= x.a <= x.b <= F(3,2):
        raise ArithmeticError("sine outside monotone range")
    return I(_trig_point(x.a,1).a, _trig_point(x.b,1).b)

def _cos(x):
    if not 0 <= x.a <= x.b <= 2:
        raise ArithmeticError("cosine outside monotone range")
    return I(_trig_point(x.b,0).a, _trig_point(x.a,0).b)

def _atan_inv(n):
    s = sum(F((-1)**j,(2*j+1)*n**(2*j+1)) for j in range(24))
    return I(s,s+F(1,49*n**49))

def _asin_point(v):
    lo, hi = F(0), F(1)
    if not 0 < v < _trig_point(hi,1).a:
        raise ArithmeticError("unsupported inverse sine")
    for _ in range(76):
        mid = (lo+hi)/2
        y = _trig_point(mid,1)
        if y.b < v:
            lo = mid
        elif y.a > v:
            hi = mid
        else:
            break  # existing bracket remains valid even if signs overlap
    return I(lo,hi)

def check_n10_area():
    """Check exact area inequalities conditional on the paper's partitions."""
    pi = 16*_atan_inv(5) - 4*_atan_inv(239)
    r = 1 + 2*_cos(pi*2/9)
    rr = r*r
    target = pi*rr
    inv = I(1)/r
    t = I(_asin_point(inv.a).a,_asin_point(inv.b).b)
    clo, chi = F('0.8846461771193156'), F('0.8846461771193158')
    p = lambda c: 4*c**3 - 2*c - 1
    if not (F(1,2) < clo**2 < chi**2 < F(4,5) and p(clo)<0<p(chi)):
        raise ArithmeticError("pentagon root isolation failed")
    c = I(clo,chi)
    rho2 = I(1)/(4*(1-c*c))
    pentagon = 2*_sqrt(rho2-F(1,4)) + _sqrt(rho2-1)
    cap = rr*(2*t-_sin(2*t))/2
    derivative = lambda s, c: s*s*c/_sqrt(rr-s*s) + (1-2*s*s)/2
    sin095 = _sin(I(F(19,20)))
    if derivative(sin095, _cos(I(F(19,20)))).b >= 0:
        raise ArithmeticError("decreasing branch check failed")
    g = _sin(pi/18)/2 + I(F(3,8))/_sqrt(rr-F(3,4)) - F(1,4)
    if g.b >= 0 or (8*pi/9).b >= pi.a or (8*pi/9-pi/2).a <= 0:
        raise ArithmeticError("shared-branch slope check failed")
    bounds = []
    for m,k,inner,limit in [(8,1,7,'20.142129866916335'),
                             (7,2,5,'19.927708248544316')]:
        y = (2*pi-2*k*t)/m
        s = r*_sin(y/2)
        if s.a <= sin095.b:
            raise ArithmeticError("Jensen evaluation outside decreasing branch")
        outer = rr*(y-_sin(y))/2 + s*_sqrt(1-s*s)
        total = m*_sin(2*pi/m) + k*pentagon + k*cap + inner + m*outer
        if not total.b < F(limit) < target.a:
            raise ArithmeticError("strict area contradiction not established")
        bounds.append(limit)
    if not (target.a > F('20.142240018608209')
            and cap.b < F('0.276753350')
            and pentagon.b < F('2.284542897111280')):
        raise ArithmeticError("directed comparison against report failed")
    return {"n": 10, "status": "directed_arithmetic_only",
            "target_area_lower": "20.142240018608209",
            "case_area_uppers": bounds, "grid_denominator": S}

def check_n10_eight_owner():
    """Directed constants for the eight-owner argument, not its geometry."""
    pi = 16*_atan_inv(5) - 4*_atan_inv(239)
    r = 1+2*_cos(pi*2/9)

    def inverse_sine(v):
        return I(_asin_point(v.a).a, _asin_point(v.b).b)

    a, b = inverse_sine(I(2)/r), inverse_sine(I(1)/r)
    psi = 2*pi-2*a-6*b
    xi = 2*pi-2*a-4*b
    u0 = I("0.3528")

    def h(angle):
        s = r*_sin(angle/4)
        return r*_cos(angle/2)-2*_cos(angle/4)*_sqrt(1-s*s)

    checks = {
        "R lower": r-"2.532", "R upper": "2.533"-r,
        "B lower": b-"0.40599", "B upper": "0.40600"-b,
        "A lower": a-"0.9105", "A upper": "0.9108"-a,
        "7B": pi-7*b, "A+5B": pi-a-5*b, "2A+3B": pi-2*a-3*b,
        "psi lower": psi-pi/2, "2A+2B": pi-2*a-2*b,
        "xi lower": xi-psi, "xi upper": pi-xi, "4B": pi-4*b,
        "u lower": (pi-6*b)/2-u0, "h(4u0)": h(4*u0)-1,
        "R derivative lower": r-"2.53",
        "sin u0": _sin(u0)-"0.34", "cos B": _cos(b)-"0.91",
        "radical": "0.52"-_sqrt(1-r*r*_sin(u0)*_sin(u0)),
        "derivative bound": I(2)*"2.53"*"0.91"*"0.34"*"0.34"/"0.52"-1,
        "R radial": r-1-_sqrt(I(2)),
        "radial comparison": (r-1)*(r-1)-(r-I(2)/r)*(r-I(2)/r)+1,
        "radial cutoff": "1.75"-(r-I(2)/r),
        "quadratic radial": r*r-2*r-F(5,4),
        "h times sine": h(pi-4*b)*_sin(psi/2)-1,
    }
    for name, margin in checks.items():
        if margin.a <= 0:
            raise ArithmeticError(f"eight-owner directed check failed: {name}")
    return {"n": 10, "status": "directed_arithmetic_only",
            "checks": list(checks), "grid_denominator": S}


if __name__ == '__main__':
    import json
    print(json.dumps({"area": check_n10_area(), "eight_owner": check_n10_eight_owner()}, indent=2))
