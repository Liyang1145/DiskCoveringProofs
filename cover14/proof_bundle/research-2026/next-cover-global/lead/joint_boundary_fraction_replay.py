"""Independent Fraction replay: joint boundary support, no optimizer or dyadic kernel."""
import json,sys,time,math
from itertools import combinations
from area_safe_fraction_replay import F,pi,L,U,sqrtv,add,neg,mul,div,point,trig,P
S=10**45
def rnd(v):return(F((v[0].numerator*S)//v[0].denominator,S),F(-((-v[1].numerator*S)//v[1].denominator),S))
def sqrtiv(v):
 lo=math.isqrt((v[0].numerator*S*S)//v[0].denominator);hi=math.isqrt((v[1].numerator*S*S)//v[1].denominator)+1;return F(lo,S),F(hi,S)
def asin1(x,N=90):
 assert 0<=x<1
 a=sum((F(math.comb(2*n,n),4**n*(2*n+1))*x**(2*n+1)for n in range(N)),F(0));return(a,a+x**(2*N+1)/(1-x*x))
def asiniv(v):
 v=rnd(v);return rnd((asin1(max(F(0),v[0]))[0],asin1(v[1])[1]))
def vmax(vs):return max(v[0]for v in vs),max(v[1]for v in vs)
gamma=rnd(div(add(L,neg(mul(point(2*U),sqrtv))),mul(point(F(2)),L)));A=rnd(mul(point(F(2)),asin1(U/2)))
def replay(q,edges,row):
 t=list(map(F,row['rational_angles']));y=list(map(F,row['rational_potentials']));mu=F(row['rational_mu']);assert mu>=0;nu=add(point(mu),gamma);bound=mul(pi,point(2*sum(y)-2*mu-1))
 for j,x in enumerate(t[:q]):
  sn,cs=map(rnd,trig(x));sh,ch=map(rnd,trig(x/2));z=mul(point(U),sh);b=point(F(0))if x==0 else mul(point(F(2)),asiniv(z));der=add(mul(point(U*U/2),cs),div(mul(mul(nu,point(U)),ch),sqrtiv(add(point(F(1)),neg(mul(z,z))))));val=add(mul(point(U*U/2),sn),mul(nu,b));slope=add(der,point(-y[j]));v1=add(add(val,neg(mul(point(x),der))),mul(pi,vmax([point(F(0)),slope])));c=mul(nu,A);v2=add(c,neg(mul(pi,point(y[j]))));bound=add(bound,vmax([v1,c,v2]));bound=rnd(bound)
 for j,(u,v)in enumerate(edges):
  x=t[q+j];sn,cs=map(rnd,trig(x));slope=add(mul(point(U*U),cs),point(-y[u]-y[v]))
  intercept=mul(point(U*U),add(sn,neg(mul(point(x),cs))))
  bound=rnd(add(bound,add(intercept,mul(pi,vmax([point(F(0)),slope])))))
 return bound
if __name__=='__main__':
 batch='--catalogue'in sys.argv;rows=[json.loads(x)for x in(P/'joint-boundary-catalogue.jsonl').read_text().splitlines()]if batch else json.loads((P/'joint-boundary-probe.json').read_text())['runs'];D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());out=[];start=time.time()
 for row in rows:
  if row['status']!='excluded':continue
  fam=row['family'];q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});v=replay(q,edges,row);assert v[1]<0
  out.append({'family':fam,'index':idx,'upper_display':float(v[1]),'upper_exact_rounded_outward':str(v[1])})
  if len(out)%50==0:print('replayed',len(out),'seconds',time.time()-start,flush=True)
 name='joint-boundary-catalogue-fraction-replay.json'if batch else'joint-boundary-fraction-replay.json';(P/name).write_text(json.dumps({'status':'independent_fraction_replay','runs':out},indent=2));print('DONE',len(out),'seconds',time.time()-start)
