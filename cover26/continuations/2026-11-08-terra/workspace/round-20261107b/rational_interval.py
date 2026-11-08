"""Outward rational interval arithmetic; every endpoint is an integer / 10^115."""
from fractions import Fraction
from math import isqrt

S=10**115

def floor_ratio(a,b):return a//b
def ceil_ratio(a,b):return -((-a)//b)

class I:
    def __init__(self,lo=0,hi=None,raw=False):
        if raw:
            self.lo,self.hi=int(lo),int(hi)
        else:
            a=Fraction(lo);b=a if hi is None else Fraction(hi)
            self.lo=a.numerator*S//a.denominator
            self.hi=ceil_ratio(b.numerator*S,b.denominator)
        if self.lo>self.hi:raise ValueError('reversed interval')
    def __add__(self,other):
        other=iv(other);return I(self.lo+other.lo,self.hi+other.hi,raw=True)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo,raw=True)
    def __sub__(self,other):return self+-iv(other)
    def __rsub__(self,other):return iv(other)+-self
    def __mul__(self,other):
        other=iv(other)
        values=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return I(min(values)//S,ceil_ratio(max(values),S),raw=True)
    __rmul__=__mul__
    def __truediv__(self,other):
        other=iv(other)
        if other.lo<=0<=other.hi:raise ValueError('divisor contains zero')
        if other.hi<0:return (-self)/(-other)
        low=min((a*S)//b for a in (self.lo,self.hi) for b in (other.lo,other.hi))
        high=max(ceil_ratio(a*S,b) for a in (self.lo,self.hi) for b in (other.lo,other.hi))
        return I(low,high,raw=True)
    def __rtruediv__(self,other):return iv(other)/self
    def square(self):
        values=[self.lo*self.lo,self.hi*self.hi]
        low=0 if self.lo<=0<=self.hi else min(values)
        return I(low//S,ceil_ratio(max(values),S),raw=True)
    def root(self):
        if self.lo<0:raise ValueError('negative radicand')
        return I(isqrt(self.lo*S),isqrt(self.hi*S)+1,raw=True)
    def abs_upper(self):return max(abs(self.lo),abs(self.hi))
    def positive(self):return self.lo>0
    def negative(self):return self.hi<0
    def lower_fraction(self):return Fraction(self.lo,S)
    def upper_fraction(self):return Fraction(self.hi,S)

def iv(x):return x if isinstance(x,I) else I(x)

def powers(box,degree=6):
    return [[I(1)]+[None]*degree for _ in box]

def evaluator(box):
    cache=[[I(1),x] for x in box]
    def evaluate(p):
        out=I(0)
        for exponents,coefficient in p.terms.items():
            term=I(coefficient)
            for j,k in enumerate(exponents):
                if k:
                    while len(cache[j])<=k:cache[j].append(cache[j][-1]*box[j])
                    term=term*cache[j][k]
            out=out+term
        return out
    return evaluate
