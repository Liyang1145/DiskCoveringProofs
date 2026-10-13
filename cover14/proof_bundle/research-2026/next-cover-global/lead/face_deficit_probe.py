"""Bounded numeric 3D boxsupport test: oneinteriorface radiusdeficit; notcertificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math,heapq,time
from itertools import combinations
from fractions import Fraction as Q
from pathlib import Path
P=Path(__file__).resolve().parent;r=.33173203427623414;a=r*r

def support(lo,hi,p):
 t=0 if p>=a else(math.pi if p<=-a else math.acos(p/a));t=max(lo,min(hi,t));return a*math.sin(t)-p*t

def boxbound(box,p):
 lo=[x[0]for x in box];hi=[x[1]for x in box];dist=max(0,sum(lo)-math.pi,math.pi-sum(hi));pen=a/2*(1-math.cos(min(lo)))*dist
 return sum(support(x,y,z)for(x,y),z in zip(box,p))-pen

def solve(p,budget=4000):
 box=[(0,math.pi)]*3;heap=[(-boxbound(box,p),0,box)];uid=0
 for k in range(budget):
  neg,_,box=heapq.heappop(heap);j=max(range(3),key=lambda j:box[j][1]-box[j][0]);lo,hi=box[j];mid=(lo+hi)/2
  for seg in [(lo,mid),(mid,hi)]:
   b=box.copy();b[j]=seg;uid+=1;heapq.heappush(heap,(-boxbound(b,p),uid,b))
 return -heap[0][0]

if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());rows=[json.loads(x)for x in(P/'joint-innernorm-catalogue.jsonl').read_text().splitlines()];out=[];start=time.time()
 for fam in ['10/4','11/3']:
  rr=sorted([x for x in rows if x['family']==fam and x['status']=='inconclusive'],key=lambda x:x['upper_display'])[:6]
  for row in rr:
   q=int(fam.split('/')[0]);idx=row['index'];faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});y=list(map(float,map(Q,row['rational_potentials'])));t=list(map(float,map(Q,row['rational_angles'])));cnt={e:sum(all(v in f for v in e)for f in faces)for e in edges};rrr=[]
   for j,f in enumerate(faces):
    ee=[tuple(sorted(e))for e in combinations(f,2)]
    if not all(cnt[e]==2 for e in ee):continue
    pot=[sum(y[v]for v in e)for e in ee];old=0
    for e,p in zip(ee,pot):
     x=t[q+edges.index(e)];old+=a*(math.sin(x)-x*math.cos(x))+math.pi*max(0,a*math.cos(x)-p)
    new=solve(pot);rrr.append({'face':j,'replacement_delta':new-old,'numeric_new_upper':row['upper_display']+new-old})
   best=min(rrr,key=lambda x:x['numeric_new_upper']);out.append({'family':fam,'index':idx,'old_upper':row['upper_display'],'best':best,'faces':rrr});print(fam,idx,best,flush=True)
 (P/'face-deficit-probe.json').write_text(json.dumps({'status':'numeric_only_4000boxsplits_perface','seconds':time.time()-start,'runs':out},indent=2))
