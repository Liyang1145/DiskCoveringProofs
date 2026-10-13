"""Independent Fraction replay of capped affine perimeter supportingplanes."""
import sys,json,time
from itertools import combinations
from area_safe_fraction_replay import F,pi,L,U,sqrtv,add,neg,mul,point,trig,P
A=F('0.333272257');k=F('0.123099267');Lb=F('0.676277969');T=(Lb-A)/k
assert L[1]<Lb and 0<T<pi[0]
R=add(mul(point(F(2)),pi),neg(mul(point(F(9)),L)));sinR=(trig(R[0])[0][0],trig(R[1])[0][1]);cap=neg(mul(point(F(1,2)),add(mul(point(18*U),sqrtv),sinR)))
batch='--catalogue'in sys.argv
rows=[json.loads(x)for x in(P/'area-capped-chord-catalogue.jsonl').read_text().splitlines()]if batch else json.loads((P/'area-capped-chord-probe.json').read_text())['runs'];D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());out=[];start=time.time()
for row in rows:
 if row['status']!='excluded':continue
 fam=row['family'];q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});t=list(map(F,row['rational_angles']));y=list(map(F,row['rational_potentials']));mu=F(row['rational_mu']);assert mu>=0
 bound=add(cap,mul(pi,point(2*(sum(y)-mu))))
 for j,x in enumerate(t):
  aa=U*U/(2 if j<q else 1);sn,cs=trig(x);bound=add(bound,mul(point(aa),add(sn,neg(mul(point(x),cs)))))
  potential=y[j]if j<q else sum(y[i]for i in edges[j-q]);slope=add(mul(point(aa),cs),point(-potential));vs=[point(mu*A),add(mul(point(T),slope),point(mu*Lb)),add(mul(pi,slope),point(mu*Lb))]if j<q else[point(F(0)),mul(pi,slope)]
  bound=add(bound,(max(v[0]for v in vs),max(v[1]for v in vs)))
 assert bound[1]<0
 out.append({'family':fam,'index':idx,'upper_display':float(bound[1]),'upper_exact_rounded_outward':str(F(-((-bound[1].numerator*10**30)//bound[1].denominator),10**30))})
 if len(out)%100==0:print('replayed',len(out),'seconds',time.time()-start,flush=True)
name='area-capped-chord-catalogue-fraction-replay.json'if batch else'area-capped-chord-fraction-replay.json';(P/name).write_text(json.dumps({'status':'independent_fraction_replay','envelope_constants_dependency':'area-chord-tighten-fraction-replay.json','runs':out},indent=2));print('DONE',len(out),'seconds',time.time()-start)
