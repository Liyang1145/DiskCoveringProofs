"""Independent Fraction replay with exact boxcoverage/disjointness audit."""
import json,math,time
from itertools import combinations
from functools import lru_cache
from joint_innernorm_fraction_replay import replay,F,pi,U,add,neg,mul,point,trig,rnd,vmax,P
@lru_cache(None)
def sc(t):return tuple(map(rnd,trig(t)))
def sub(a,b):return add(a,neg(b))
def oldedge(t,p):
 sn,cs=sc(t);slope=add(mul(point(U*U),cs),point(-p));return add(mul(point(U*U),sub(sn,mul(point(t),cs))),mul(pi,vmax([point(F(0)),slope])))
def sup(lo,hi,p):
 a=mul(pi,point(lo));b=mul(pi,point(hi));opt=0 if float(p)>=float(U*U)else(math.pi if float(p)<=-float(U*U)else math.acos(float(p/(U*U))));tf=max(float(lo)*math.pi,min(float(hi)*math.pi,opt));t=max(F(0),min(F('3.141592653589'),F(format(tf,'.12f'))));sn,cs=sc(t);slope=add(mul(point(U*U),cs),point(-p));return add(mul(point(U*U),sub(sn,mul(point(t),cs))),vmax([mul(a,slope),mul(b,slope)]))
def cosiv(v):
 mid=(v[0]+v[1])/2;_,cs=sc(mid);err=(v[1]-v[0])/2;return(cs[0]-err,cs[1]+err)
def checkboxes(boxes):
 assert all(F(0)<=a<b<=F(1)for box in boxes for a,b in box)
 assert sum((math.prod(b-a for a,b in box)for box in boxes),F(0))==1
 for b1,b2 in combinations(boxes,2):assert any(max(a,c)>=min(b,d)for(a,b),(c,d)in zip(b1,b2))
def verify(q,edges,faces,row,cert):
 t=list(map(F,row['rational_angles']));y=list(map(F,row['rational_potentials']));ee=[tuple(sorted(e))for e in combinations(faces[cert['face']],2)];assert all(sum(all(v in f for v in e)for f in faces)==2 for e in ee);p=[sum(y[v]for v in e)for e in ee];base=replay(q,edges,row)
 for e,pp in zip(ee,p):base=sub(base,oldedge(t[q+edges.index(e)],pp))
 boxes=[[(F(a),F(b))for a,b in box]for box in cert['leaves']];checkboxes(boxes);vals=[]
 for box in boxes:
  lo=[v[0]for v in box];hi=[v[1]for v in box];dist=mul(pi,point(max(F(0),sum(lo)-1,1-sum(hi))));pen=mul(point(U*U/2),mul(sub(point(F(1)),cosiv(mul(pi,point(min(lo))))),dist));b=point(F(0))
  for(a,c),pp in zip(box,p):b=add(b,sup(a,c,pp))
  vals.append(sub(b,pen))
 return rnd(add(base,vmax(vals)))
if __name__=='__main__':
 import sys
 batch='--catalogue'in sys.argv;filename='face-deficit-catalogue.jsonl'if batch else'face-deficit-certificate.json'
 certs=[json.loads(x)for x in(P/filename).read_text().splitlines()]if batch else json.loads((P/filename).read_text())['runs'];D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());rows={(x['family'],x['index']):x for x in[json.loads(x)for x in(P/'joint-innernorm-catalogue.jsonl').read_text().splitlines()]};out=[];start=time.time()
 for c in certs:
  if c['status']!='excluded':continue
  fam=c['family'];idx=c['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});b=verify(q,edges,faces,rows[fam,idx],c);assert b[1]<0;out.append({'family':fam,'index':idx,'face':c['face'],'upper_display':float(b[1]),'upper_exact_outward':str(b[1]),'boxes_checked':len(c['leaves'])});print('replayed',len(out),'seconds',time.time()-start,flush=True)
 name='face-deficit-catalogue-fraction-replay.json'if batch else'face-deficit-fraction-replay.json';(P/name).write_text(json.dumps({'status':'independent_fraction_and_exact_partition_replay','runs':out},indent=2))
