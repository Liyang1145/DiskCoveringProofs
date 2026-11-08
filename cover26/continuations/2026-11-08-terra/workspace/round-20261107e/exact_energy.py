"""Exact normalized Dirichlet-energy minorants on closed angular boxes."""
from pathlib import Path
from fractions import Fraction as Q
import json,sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'round-20261107b'))
from rational_interval import I
sys.path.insert(0,str(HERE.parent/'round-20261107d/native-source'))
import exact_arcs as arcs

def floor(q):return q.numerator//q.denominator
def ceil(q):return -floor(-q)

def cos_lower(lo,hi):
    if hi-lo>=1:return Q(-1)
    value=min(arcs.sincos_turn(lo)[0][0],arcs.sincos_turn(hi)[0][0])
    if ceil(lo-Q(1,2))<=floor(hi-Q(1,2)):value=-arcs.SCALE
    return Q(value,arcs.SCALE)

def data(kernel,leaf,parts):
    if type(parts)is not int or not 1<=parts<=128:raise ValueError('Taylor strip count')
    ref=[Q(0),*map(Q,kernel['reference_turns'])]
    lo=[Q(0),*map(Q,leaf['lower'])];hi=[Q(0),*map(Q,leaf['upper'])]
    if len(ref)!=16 or any(a>b for a,b in zip(lo,hi)):raise ValueError('closed source domain')
    grid=int(kernel['coefficient_denominator'])
    pi=I(Q(arcs.PI[0],arcs.SCALE),Q(arcs.PI[1],arcs.SCALE))
    energy=I(Q(int(kernel['constant_lower']),grid));gradient=[I(0) for _ in range(16)]
    H=[[Q(0)]*15 for _ in range(15)];rounding=10**20
    for i,j,numerator,_ in kernel['pairs']:
        c=Q(int(numerator),grid)
        if c<0:raise ValueError('negative pair coefficient')
        difference=ref[j]-ref[i]
        co,si=arcs.sincos_turn(difference)
        cosine=I(Q(co[0],arcs.SCALE),Q(co[1],arcs.SCALE))
        sine=I(Q(si[0],arcs.SCALE),Q(si[1],arcs.SCALE))
        energy=energy+2*c*(1-cosine)
        derivative=4*c*pi*sine
        gradient[i]=gradient[i]-derivative;gradient[j]=gradient[j]+derivative
        leftdiff,rightdiff=lo[j]-hi[i],hi[j]-lo[i]
        combined=Q(0)
        factor=8*c*pi.square()
        for k in range(parts):
            a,b=Q(k,parts),Q(k+1,parts)
            endpoints=[difference+t*(x-difference) for t in (a,b) for x in (leftdiff,rightdiff)]
            minimum=cos_lower(min(endpoints),max(endpoints))
            lower=(factor*minimum).lower_fraction()
            combined+=Q(2*parts-2*k-1,parts*parts)*lower
        h=Q(floor(combined*rounding),rounding)
        if i:H[i-1][i-1]+=h
        if j:H[j-1][j-1]+=h
        if i and j:H[i-1][j-1]-=h;H[j-1][i-1]-=h
    low=[a-r for a,r in zip(lo[1:],ref[1:])];high=[b-r for b,r in zip(hi[1:],ref[1:])]
    g=[(x.lower_fraction()+x.upper_fraction())/2 for x in gradient[1:]]
    error=sum((x.upper_fraction()-x.lower_fraction())/2*max(abs(a),abs(b)) for x,a,b in zip(gradient[1:],low,high))
    return {'reference':ref,'lower_delta':low,'upper_delta':high,'hessian':H,
            'reference_energy_lower':energy.lower_fraction(),'gradient':g,'gradient_error':error}

def positive_ldl(matrix):
    n=len(matrix);L=[[Q(0)]*n for _ in range(n)];D=[]
    for i in range(n):
        value=matrix[i][i]-sum(L[i][k]**2*D[k] for k in range(i))
        if value<=0:raise ValueError('quadratic minorant is not exact positive definite')
        D.append(value);L[i][i]=1
        for j in range(i+1,n):
            L[j][i]=(matrix[j][i]-sum(L[j][k]*L[i][k]*D[k] for k in range(i)))/value
    return D

def quadratic(info,correction):
    eta=list(map(Q,correction))
    if len(eta)!=15 or min(eta)<0:raise ValueError('nonnegative curvature correction required')
    H=info['hessian']
    matrix=[[v+(eta[i] if i==j else 0) for j,v in enumerate(row)] for i,row in enumerate(H)]
    pivots=positive_ldl(matrix)
    lo,hi=info['lower_delta'],info['upper_delta']
    linear=[g-e*(a+b)/2 for g,e,a,b in zip(info['gradient'],eta,lo,hi)]
    constant=info['reference_energy_lower']-info['gradient_error']+sum(e*a*b/2 for e,a,b in zip(eta,lo,hi))
    return matrix,linear,constant,pivots

def evaluate(info,correction,point,dual,matrix,scale):
    Qmat,linear,constant,pivots=quadratic(info,correction)
    point=list(map(Q,point))
    if len(point)!=15:raise ValueError('quadratic tangent dimension')
    Qp=[sum(a*b for a,b in zip(row,point)) for row in Qmat]
    tangent=[a+b for a,b in zip(Qp,linear)]
    constant-=sum(x*y for x,y in zip(point,Qp))/2
    ref=info['reference'];q=int(dual['denominator'])
    if q<=0:raise ValueError('positive dual denominator')
    seen=set()
    for i,j,n in dual['terms']:
        if type(i)is not int or type(j)is not int or not 0<=i<16 or not 0<=j<16 or i==j or (i,j) in seen:
            raise ValueError('invalid directed difference dual')
        seen.add((i,j));multiplier=Q(int(n),q)
        if multiplier<0:raise ValueError('negative directed difference dual')
        if j:tangent[j-1]+=multiplier
        if i:tangent[i-1]-=multiplier
        rhs=Q(int(matrix[i][j]),scale)-(ref[j]-ref[i])
        constant-=multiplier*rhs
    value=constant+sum(min(v*a,v*b) for v,a,b in zip(tangent,info['lower_delta'],info['upper_delta']))
    return value,pivots
