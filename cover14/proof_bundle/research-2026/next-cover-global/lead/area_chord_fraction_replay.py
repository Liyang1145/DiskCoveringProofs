"""Independent Fraction check: affine envelope and chord-enhanced planes."""
import json,math,sys,time
from itertools import combinations
from area_safe_fraction_replay import F,pi,L,U,sqrtv,add,neg,mul,div,point,trig,P,replay,capminus

def sqrtenclose(v):
 scale=10**65;low=math.isqrt((v[0].numerator*scale*scale)//v[0].denominator);high=math.isqrt((v[1].numerator*scale*scale)//v[1].denominator)+1
 return(F(low,scale),F(high,scale))
def asinpoint(x,N=90):
 a=sum((F(math.comb(2*n,n),4**n*(2*n+1))*x**(2*n+1)for n in range(N)),F(0));return(a,a+x**(2*N+1)/(1-x*x))
tight='--tight'in sys.argv
A=F('0.333272257')if tight else F(167,500);k=F('0.123099267')if tight else F(31,250);alpha0=F('2.420575')if tight else F(121,50);sn,cs=trig(alpha0/2);z=mul(point(U),sn);f=(2*asinpoint(z[0])[0],2*asinpoint(z[1])[1]);fp=div(mul(point(U),cs),sqrtenclose(add(point(F(1)),neg(mul(z,z)))));b=add(f,neg(mul(point(alpha0),fp)))
assert 2*asinpoint(U/2)[1]<A and fp[1]<k and b[1]<A
R=add(mul(point(F(2)),pi),neg(mul(point(F(9)),L)));sinR=(trig(R[0])[0][0],trig(R[1])[0][1]);sharp=neg(mul(point(F(1,2)),add(mul(point(18*U),sqrtv),sinR)))
batch='--catalogue'in sys.argv
rows=[json.loads(x)for x in(P/'area-chord-catalogue.jsonl').read_text().splitlines()]if batch else json.loads((P/('area-chord-tighten.json'if tight else'area-chord-probe.json')).read_text())['runs']
D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());out=[];start=time.time()
for row in rows:
 if row['status']!='excluded':continue
 fam=row['family'];q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});t=list(map(F,row['rational_angles']));y=list(map(F,row['rational_potentials']));mu=F(row['rational_mu']);assert mu>=0
 K=div(add(mul(point(F(2)),pi),point(-q*A)),point(k));bound=add(sharp,add(mul(pi,point(2*sum(y))),neg(mul(point(mu),K))))
 for j,x in enumerate(t):
  aa=U*U/(2 if j<q else 1);sn,cs=trig(x);bound=add(bound,mul(point(aa),add(sn,neg(mul(point(x),cs)))))
  potential=y[j]if j<q else sum(y[i]for i in edges[j-q]);slope=add(mul(point(aa),cs),point(-potential+(mu if j<q else F(0))));bound=add(bound,mul(pi,(max(F(0),slope[0]),max(F(0),slope[1]))))
 assert bound[1]<0
 out.append({'family':fam,'index':idx,'upper_display':float(bound[1]),'upper_exact_rounded_outward':str(F(-((-bound[1].numerator*10**30)//bound[1].denominator),10**30))})
 if len(out)%100==0:print('replayed',len(out),'seconds',time.time()-start,flush=True)
name='area-chord-catalogue-fraction-replay.json'if batch else('area-chord-tighten-fraction-replay.json'if tight else'area-chord-fraction-replay.json')
(P/name).write_text(json.dumps({'status':'independent_fraction_replay','envelope_constants_certified':True,'runs':out},indent=2));print('DONE',len(out),'seconds',time.time()-start)
