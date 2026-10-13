"""Directed interval 3D support certificate with radiusdeficit; dyadicboxes partition[0,pi]^3."""
import json,math,heapq,time
from itertools import combinations
from functools import lru_cache
from joint_innernorm_probe import verify,I,Q,S,PI,U,trig,P
@lru_cache(None)
def sc(t):return trig(I(t))
@lru_cache(None)
def costerm(t):return trig(PI*I(t))[1]
def edgeold(x,p):
 sn,cs=sc(x);slope=I(U*U)*cs-p
 return I(U*U)*(sn-I(x)*cs)+PI*I(max(0,slope.lo),max(0,slope.hi),True)
def support(lo,hi,p,opt):
 a=PI*I(lo);b=PI*I(hi);tf=max(float(lo)*math.pi,min(float(hi)*math.pi,opt));t=max(Q(0),min(Q('3.141592653589'),Q(format(tf,'.12f'))));sn,cs=sc(t);slope=I(U*U)*cs-p;vv=[a*slope,b*slope]
 return I(U*U)*(sn-I(t)*cs)+I(max(x.lo for x in vv),max(x.hi for x in vv),True)
def boxbound(box,p,opts):
 lo=[v[0]for v in box];hi=[v[1]for v in box];dist=I(max(Q(0),sum(lo)-1,1-sum(hi)))*PI;pen=I(U*U/2)*(1-costerm(min(lo)))*dist
 return sum((support(a,b,y,o)for(a,b),y,o in zip(box,p,opts)),I(0))-pen

def certify(q,edges,faces,row,face,budget=4000):
 t=list(map(Q,row['rational_angles']));y=list(map(Q,row['rational_potentials']));nu=Q(row['rational_nu']);lam=Q(row['rational_lambda']);total=verify(q,edges,t,y,nu,lam);ee=[tuple(sorted(e))for e in combinations(faces[face],2)]
 assert all(sum(all(v in f for v in e)for f in faces)==2 for e in ee)
 p=[sum(y[v]for v in e)for e in ee];base=total-sum((edgeold(t[q+edges.index(e)],pp)for e,pp in zip(ee,p)),I(0));opts=[0 if float(v)>=float(U*U)else(math.pi if float(v)<=-float(U*U)else math.acos(float(v/(U*U))))for v in p]
 box=[(Q(0),Q(1))]*3;b=boxbound(box,p,opts);heap=[(-b.hi,0,box)];uid=0
 for k in range(budget):
  if base.hi-heap[0][0]<0:break
  neg,_,box=heapq.heappop(heap);j=max(range(3),key=lambda j:box[j][1]-box[j][0]);lo,hi=box[j];mid=(lo+hi)/2
  for seg in[(lo,mid),(mid,hi)]:
   b=box.copy();b[j]=seg;uid+=1;v=boxbound(b,p,opts);heapq.heappush(heap,(-v.hi,uid,b))
 upper=base.hi-heap[0][0]
 return {'family':row['family'],'index':row['index'],'face':face,'status':'excluded'if upper<0 else'inconclusive','upper_display':upper/S,'upper_exact':str(Q(upper,S)),'base_upper_exact':str(Q(base.hi,S)),'leaf_count':len(heap),'leaves':[[[str(a),str(b)]for a,b in box]for neg,uid,box in heap]}
if __name__=='__main__':
 import sys
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());rows={(x['family'],x['index']):x for x in[json.loads(x)for x in(P/'joint-innernorm-catalogue.jsonl').read_text().splitlines()]};probes=json.loads((P/'face-deficit-probe.json').read_text())['runs'];out=[];start=time.time()
 for test in probes:
  if test['best']['numeric_new_upper']>=0:continue
  fam=test['family'];idx=test['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=certify(q,edges,faces,rows[fam,idx],test['best']['face']);out.append(rec);print(fam,idx,rec['status'],rec['upper_display'],'leaves',rec['leaf_count'],'seconds',time.time()-start,flush=True)
 (P/'face-deficit-certificate.json').write_text(json.dumps({'status':'interval_bounds_analytic_radiusdeficit','runs':out},indent=2))
