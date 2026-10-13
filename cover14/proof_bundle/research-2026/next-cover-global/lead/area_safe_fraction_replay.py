"""Independent exact Fraction replay: no fixed-dyadic I or optimizer is used.
Taylor at exact rational points, rational interval endpoints combine constants.
"""
from fractions import Fraction as F
import json,math
from pathlib import Path
from itertools import combinations
P=Path(__file__).resolve().parent
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[1],-a[0])
def mul(a,b):
 x=[u*v for u in a for v in b];return(min(x),max(x))
def div(a,b):assert b[0]>0;return mul(a,(1/b[1],1/b[0]))
def point(a):return(a,a)
def atan(x,N=80):
 z=sum(((-1)**n*x**(2*n+1)/(2*n+1)for n in range(N)),F(0));v=z+(-1)**N*x**(2*N+1)/(2*N+1);return(min(z,v),max(z,v))
pi=add(mul(point(F(16)),atan(F(1,5))),neg(mul(point(F(4)),atan(F(1,239)))))
U=F('0.33173203427623414');N=90
alo=sum((F(math.comb(2*k,k),4**k*(2*k+1))*U**(2*k+1)for k in range(N)),F(0));L=(2*alo,2*(alo+U**(2*N+1)/(1-U*U)))
# Independent sqrt enclosure using rational scale 10^65 and integer floor root.
v=1-U*U;scale=10**65;root=math.isqrt((v.numerator*scale*scale)//v.denominator);sqrtv=(F(root,scale),F(root+1,scale));assert sqrtv[0]**2<=v<=sqrtv[1]**2
capminus=neg(div(mul(mul(pi,point(2*U)),sqrtv),L))
def trig(x):
 assert 0<=x<=pi[0]
 sn=sum(((-1)**k*x**(2*k+1)/math.factorial(2*k+1)for k in range(30)),F(0))
 cs=sum(((-1)**k*x**(2*k)/math.factorial(2*k)for k in range(31)),F(0))
 # sin polynomialdegree60 (evencoefficient0), cosdegree60, commonLagrangeremainder.
 err=x**61/math.factorial(61)
 return(sn-err,sn+err),(cs-err,cs+err)
def replay(q,edges,t,y):
 bound=add(capminus,mul(pi,point(2*sum(y))))
 for j,x in enumerate(t):
  a=U*U/(2 if j<q else 1);sn,cs=trig(x)
  bound=add(bound,mul(point(a),add(sn,neg(mul(point(x),cs)))))
  potential=y[j]if j<q else sum(y[i]for i in edges[j-q]);slope=add(mul(point(a),cs),point(-potential));bound=add(bound,mul(pi,(max(F(0),slope[0]),max(F(0),slope[1]))))
 return bound
if __name__=='__main__':
 import sys,time
 batch='--catalogue' in sys.argv
 D=json.loads((P/'q11-pocket-catalogue.json').read_text());D10=json.loads((P/'k10-catalogue-corrected.json').read_text())
 cert=[json.loads(line)for line in(P/'area-safe-catalogue.jsonl').read_text().splitlines()]if batch else json.loads((P/'area-safe-certificate.json').read_text())['runs'];out=[];start=time.time()
 for k,rec in enumerate(cert):
  if batch and rec['status']!='excluded':continue
  idx=rec['index'];family=rec.get('family','11/3');q=int(family.split('/')[0]);faces=D['entries'][idx]['faces']if q==11 else D10[family][idx]['faces']
  edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});t=list(map(F,rec['rational_angles']));y=list(map(F,rec['rational_node_potentials']));bound=replay(q,edges,t,y)
  assert (bound[1]<0)==(rec['status']=='excluded')
  out.append({'index':idx,'family':family,'excluded':bound[1]<0,'upper_display':float(bound[1]),'upper_exact_rounded_outward':str(F(-((-bound[1].numerator*10**30)//bound[1].denominator),10**30))})
  if len(out)%100==0:print('replayed',len(out),'seconds',time.time()-start,flush=True)
 name='area-safe-catalogue-fraction-replay.json'if batch else'area-safe-fraction-replay.json'
 (P/name).write_text(json.dumps({'status':'independent_fraction_replay','scope':'all excluded rows only'if batch else'12 calibration rows','runs':out},indent=2));print('DONE',len(out),'seconds',time.time()-start)
