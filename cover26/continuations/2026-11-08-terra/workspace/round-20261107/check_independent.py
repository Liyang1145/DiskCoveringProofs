"""Independent Fraction-based replay of the shifted-fan scalar certificate.

No JS, cached certificate, optimizer output, or float enters acceptance.
The Voronoi geometry is supplied by PROOF.md and the earlier proof chain.
"""
from fractions import Fraction as F
from math import isqrt, factorial
import argparse
import json

parser=argparse.ArgumentParser()
parser.add_argument('--negative-control', action='store_true')
args=parser.parse_args()
K=10**22

def demand(p,message):
    if not p:
        raise ValueError(message)

def round_down(x):
    return F(x.numerator*K//x.denominator,K)

def round_up(x):
    return -round_down(-x)

class Interval:
    def __init__(self, lo, hi=None):
        self.lo=F(lo)
        self.hi=self.lo if hi is None else F(hi)
        demand(self.lo<=self.hi,'reversed interval')
    def __add__(self, other):
        other=interval(other)
        return Interval(round_down(self.lo+other.lo),round_up(self.hi+other.hi))
    __radd__=__add__
    def __neg__(self):
        return Interval(-self.hi,-self.lo)
    def __sub__(self, other):
        return self+-interval(other)
    def __rsub__(self, other):
        return interval(other)+-self
    def __mul__(self, other):
        other=interval(other)
        values=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Interval(round_down(min(values)),round_up(max(values)))
    __rmul__=__mul__
    def __truediv__(self, other):
        other=interval(other)
        demand(other.lo>0,'division domain')
        values=[a/b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Interval(round_down(min(values)),round_up(max(values)))
    def __rtruediv__(self, other):
        return interval(other)/self
    def square(self):
        demand(self.lo>=0,'square domain')
        return self*self
    def root(self):
        demand(self.lo>=0,'root domain')
        low=isqrt(self.lo.numerator*K*K//self.lo.denominator)
        high=isqrt(self.hi.numerator*K*K//self.hi.denominator)+1
        demand(F(low,K)**2<=self.lo and F(high,K)**2>self.hi,'root enclosure')
        return Interval(F(low,K),F(high,K))

def interval(x):
    return x if isinstance(x,Interval) else Interval(x)

def greater(x,y):
    return interval(x).lo>interval(y).hi

def trig_point(x,cosine=False):
    demand(0<=x<=1,'Taylor domain')
    # Ten terms end with a negative term, and eleven end with a positive term.
    terms=[(-1)**j*x**(2*j+(0 if cosine else 1))/factorial(2*j+(0 if cosine else 1))
           for j in range(11)]
    low=sum(terms[:10],F(0));high=low+terms[10]
    return round_down(low),round_up(high)

def sine(x):
    x=interval(x)
    return Interval(trig_point(x.lo)[0],trig_point(x.hi)[1])

def cosine(x):
    x=interval(x)
    return Interval(trig_point(x.hi,True)[0],trig_point(x.lo,True)[1])

def atan_inverse(n):
    # Thirty even-count terms give a lower alternating sum.
    low=sum((F((-1)**j,(2*j+1)*n**(2*j+1)) for j in range(30)),F(0))
    return Interval(low,low+F(1,61*n**61))

machin=16*atan_inverse(5)-4*atan_inverse(239)
PI=Interval(F(314159265358979323846,10**20),F(314159265358979323847,10**20))
demand(PI.lo<machin.lo and machin.hi<PI.hi,'independent Machin enclosure')
radius=F(230001 if args.negative_control else 229001,10**6)
U=Interval(radius);U2=U.square();A=3*Interval(3).root()/4
BASE=F(387,10000);EAR=F(97,1000)
CAP=F(1101,500)
demand(greater(A+F(1,2)-F(147325,83694),BASE),'Young deficit')
demand(greater(CAP,(F(9,4)+F(3,2)*Interval(3).root()).root()),'Heron maximum')
demand(greater(A+1-CAP,EAR),'ear deficit')
demand(greater(sine(PI/13),U) and greater(1,5*U2),'normalization domain')

def G(t):
    s=sine(t)
    return t-s*cosine(t)+s*(U2-s.square()).root()

config={16:(F(8,100),F(2,100),(-52500,36300),(-67300,42300)),
        17:(F(6,100),F(0),(-32400,24600),(-33900,25400)),
        18:(F(44,1000),F(0),(-17400,15300),None)}

# These supports are checked independently, including their positive slopes.
one_support=[]
for k in range(1100,1611,10):
    z=Interval(F(k,1000));h=(1-z.square()/4).root()
    derivative=F(1,2)+(1-z.square()/2)/h
    if greater(derivative,0):
        one_support.append((z,z/2+z*h,derivative))
ear_support=[]
for k in range(2500,5401,100):
    z=Interval(F(k,1000));h=(z*(8-z)).root()
    value=(z+h)/4 if k<=4000 else (z+4)*h/16
    derivative=F(1,4)+(4-z)/(4*h) if k<=4000 else (-z.square()+4*z+8)/(8*h)
    demand(greater(derivative,0),'ear support slope')
    ear_support.append((z,value,derivative))

cases=[]
for b in range(14,27):
    d=PI/b
    e,shift,window,ear_window=config.get(b,(BASE,F(0),None,None))
    anchor=d-shift
    demand(greater(anchor,0) and greater(U,sine(anchor)),'anchor domain')
    s=sine(anchor);h=(U2-s.square()).root()
    slope=2*s.square()+cosine(anchor)*(U2-2*s.square())/h
    tangent_at_mean=G(anchor)+slope*(d-anchor)
    upper=(50-b)*A*U2+b*U2*(F(1,2)-e)+b*tangent_at_mean
    if not greater(PI,upper):
        if args.negative_control:
            print(json.dumps({'passed':True,'control':'reject larger radius','rejected_owner_count':b}))
            raise SystemExit(0)
        raise ValueError('global area contradiction at b='+str(b))
    cached={}
    def at(offset):
        if offset not in cached:
            t=anchor+F(offset,10**6);s=sine(t);c=cosine(t)
            demand(greater(t,0) and greater(U,s),'window domain')
            h=(U2-s.square()).root()
            cached[offset]=(s,c-h,G(anchor)+slope*F(offset,10**6)-(t-s*c+s*h))
        return cached[offset]
    def jlower(lo,hi):
        return max(F(0),at(lo)[2].lo if lo>0 else at(hi)[2].lo if hi<0 else F(0))
    def edge(lo,hi,low,high):
        amin,amax,bmin,bmax=at(lo)[1],at(hi)[1],at(low)[1],at(high)[1]
        demand(amin.lo>0 and bmin.lo>0,'positive ideal radius')
        diff=Interval(max(F(0),amax.hi-bmin.lo,bmax.hi-amin.lo))
        angle=anchor+F(hi+high,2*10**6)
        return (diff.square()+4*amax*bmax*sine(angle).square()).root()/U
    one_count=ear_count=0
    if window:
        budget=2*(e-BASE)*U2
        lo,hi=window
        demand(greater(at(lo)[2],budget) and greater(at(hi)[2],budget),'one-edge full window')
        stack=[(lo,hi,lo,hi)]
        while stack:
            lo,hi,low,high=stack.pop();one_count+=1
            demand(one_count<500000,'one-edge subdivision limit')
            J=Interval(jlower(lo,hi)+jlower(low,high))
            if greater(J,budget):
                continue
            ell=edge(lo,hi,low,high)
            smin=Interval(min(at(lo)[0].lo,at(low)[0].lo))
            remaining=Interval(max(F(0),budget.hi-J.lo))
            fixed=A+F(1,2)+J/(2*U2)
            for z,value,derivative in one_support:
                coeff=1/(2*U2)-derivative/smin.square()
                loss=fixed-value-derivative*(ell-z)+Interval(min(F(0),coeff.lo))*remaining
                if greater(loss,e):
                    break
            else:
                demand(max(hi-lo,high-low)>1,'unresolved one-edge box')
                if hi-lo>=high-low:
                    mid=(lo+hi)//2;stack.extend([(lo,mid,low,high),(mid,hi,low,high)])
                else:
                    mid=(low+high)//2;stack.extend([(lo,hi,low,mid),(lo,hi,mid,high)])
        if ear_window:
            budget=(2*e-EAR)*U2
            lo,hi=ear_window
            demand(greater(at(lo)[2],2*budget) and greater(at(hi)[2],2*budget),'ear full window')
            stack=[(lo,hi,lo,hi,lo,hi,F(0),budget.hi)]
            while stack:
                box=stack.pop();lo,hi,low,high,left,right,tlo,thi=box;ear_count+=1
                demand(ear_count<1000000,'ear subdivision limit')
                J=Interval((jlower(lo,hi)+2*jlower(low,high)+jlower(left,right))/2)
                if greater(J+tlo,budget):
                    continue
                capped=min(thi,max(F(0),budget.hi-J.lo))
                demand(tlo<=capped,'empty residual interval')
                if greater(A+1-CAP+(J+tlo)/U2,2*e):
                    continue
                ell1=edge(lo,hi,low,high);ell2=edge(low,high,left,right)
                ss=[Interval(at(k)[0].lo).square() for k in (lo,low,left)]
                for z,value,derivative in ear_support:
                    passed=True
                    for t in (tlo,capped):
                        for vertex in range(3):
                            v=Interval(t*(1 if vertex==1 else 2))/ss[vertex]
                            x=ell1+(v if vertex<2 else 0)
                            y=ell2+(v if vertex>0 else 0)
                            loss=A+1-value-derivative*(x.square()+y.square()-z)+(J+t)/U2
                            if not greater(loss,2*e):
                                passed=False;break
                        if not passed:
                            break
                    if passed:
                        break
                else:
                    widths=[hi-lo,high-low,right-left];widest=max(widths)
                    # Entirely rational split selection; both closed children are retained.
                    if (capped-tlo)*10**6>2*widest*U2.lo:
                        mid=(tlo+capped)/2
                        stack.extend([(*box[:6],tlo,mid),(*box[:6],mid,capped)])
                    else:
                        demand(widest>1,'unresolved ear box')
                        dim=widths.index(widest)
                        first=list(box[:6]);second=list(box[:6]);mid=(first[2*dim]+first[2*dim+1])//2
                        first[2*dim+1]=mid;second[2*dim]=mid
                        stack.extend([(*first,tlo,capped),(*second,tlo,capped)])
        else:
            demand(EAR>2*e,'ear baseline pays both edges')
    else:
        demand(EAR>2*BASE,'base grouping')
    gap=PI.lo-upper.hi
    demand(gap>F(1,1000),'strict area gap exceeds .001')
    cases.append({'b':b,'one_edge_boxes':one_count,'two_edge_boxes':ear_count,
                  'gap_lower':str(gap)})
    print('verified b',b,'one-edge boxes',one_count,'ear boxes',ear_count,flush=True)

demand(not args.negative_control,'negative control unexpectedly passed')
print(json.dumps({'passed':True,'radius':str(radius),'cases':cases,
                  'scope':'scalar certificate; written geometric proof required'},indent=2))
