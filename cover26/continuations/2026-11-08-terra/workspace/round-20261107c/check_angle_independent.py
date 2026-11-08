"""Independently replay the entire angular domain using rational Horner bounds."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import json,sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'round-20261107b'))
from rational_interval import I

def demand(p,message):
    if not p:raise ValueError(message)

def atan_inverse(q):
    low=sum((Q((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(40)),Q(0))
    return I(low,low+Q(1,81*q**81))

PI=16*atan_inverse(5)-4*atan_inverse(239)
sqrt3=I(3).root();A=3*sqrt3/4;K=Q(4,5);H=Q(1,5);ETA=Q(3,50);MU=Q(31,50)
demand((PI/6-ETA).positive(),'core angle domain')
# The sine bound at pi/3+eta uses exact short rational Taylor endpoints.
def cos_point(x):
    lower=sum(((-1)**j*x**(2*j)/factorial(2*j) for j in range(12)),Q(0))
    return I(lower,lower+x**24/factorial(24))
def sin_point(x):
    lower=sum(((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(12)),Q(0))
    return I(lower,lower+x**25/factorial(25))
core_sine=sqrt3*cos_point(ETA)/2+sin_point(ETA)/2
demand((1-Q(31,25)*core_sine.square()).positive(),'log-sine core curvature')
demand((A*MU*(1-MU*3*ETA*ETA/2)-K).positive(),'core coefficient')

# h(delta)=delta^2 P(delta), with coefficients evaluated independently by Horner.
coeff=[I(0) for _ in range(48)]
for j in range(1,25):
    coeff[2*j-2]=sqrt3*Q((-1)**(j+1)*2**(2*j),4*factorial(2*j))
    coeff[2*j-1]=I(Q((-1)**j*2**(2*j+1),4*factorial(2*j+1)))
error=(sqrt3*Q(5**50,4*factorial(50))+Q(5**51,4*factorial(51))).upper_fraction()

def branch(delta,kind):
    demand(delta.lower_fraction()>=-Q(5,2) and delta.upper_fraction()<=Q(5,2),'Taylor remainder domain')
    coefficients=coeff.copy()
    if kind=='core':coefficients[0]=coefficients[0]-K
    value=I(0)
    for coefficient in reversed(coefficients):value=value*delta+coefficient
    value=value*delta.square()+I(-error,error)
    if kind!='core':
        absolute=delta if kind=='positive' else -delta
        value=value-K*(2*H*absolute-H*H)
    return value

def term(delta):
    lo,hi=delta.lower_fraction(),delta.upper_fraction();parts=[]
    if lo<-H:parts.append(branch(I(lo,min(hi,-H)),'negative'))
    if hi>=-H and lo<=H:parts.append(branch(I(max(lo,-H),min(hi,H)),'core'))
    if hi>H:parts.append(branch(I(max(lo,H),hi),'positive'))
    demand(parts,'Huber domain')
    return I(min(p.lower_fraction() for p in parts),max(p.upper_fraction() for p in parts))

certificate=json.loads((HERE/'ANGLE-CERTIFICATE.json').read_text())
leaflist=certificate['leaves'];leaves={tuple(row['box']) for row in leaflist}
GRID=1048576
demand(len(leaves)==len(leaflist),'unique angular leaves')
for a,b,c,d in leaves:demand(0<=a<b<=GRID and 0<=c<d<=GRID,'leaf endpoints')
# Reconstruct the binary partition instead of trusting a reported box count.
partition=[(0,GRID,0,GRID)];visited=set()
while partition:
    box=partition.pop()
    if box in leaves:visited.add(box);continue
    a,b,c,d=box
    demand(max(b-a,d-c)>1,'missing angular domain')
    if b-a>=d-c:
        mid=(a+b)//2;partition.extend([(a,mid,c,d),(mid,b,c,d)])
    else:
        mid=(c+d)//2;partition.extend([(a,b,c,mid),(a,b,mid,d)])
demand(visited==leaves,'extraneous or overlapping leaves')

stack=list(leaves);processed=analytic=interval=refinements=0
while stack:
    box=stack.pop();vl,vh,ul,uh=box;processed+=1
    demand(processed<300000,'independent refinement limit')
    w=(PI/3)*I(Q(vl,GRID),Q(vh,GRID))
    if (I(ETA)-2*w).positive():analytic+=1;continue
    u=I(Q(ul,GRID),Q(uh,GRID))
    deltas=[-w,w*(Q(3,2)*u-1),w*(2-Q(3,2)*u)]
    value=sum((term(d) for d in deltas),I(0))
    if value.positive():interval+=1;continue
    demand(max(vh-vl,uh-ul)>1,'unresolved independent box')
    if vh-vl>=uh-ul:
        mid=(vl+vh)//2;stack.extend([(vl,mid,ul,uh),(mid,vh,ul,uh)])
    else:
        mid=(ul+uh)//2;stack.extend([(vl,vh,ul,mid),(vl,vh,mid,uh)])
    refinements+=1

print(json.dumps({'passed':True,'original_leaves':len(leaves),'processed_boxes':processed,
    'analytic_leaves':analytic,'interval_leaves':interval,'independent_refinements':refinements,
    'scope':'triangle-angle lemma only; no new global 26-disk bound'},indent=2))
