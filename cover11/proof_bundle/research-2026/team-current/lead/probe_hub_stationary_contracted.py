"""Bounded experiment: can gradient cancellation+positive curvature exclude low-distance interior maxima?"""
from pathlib import Path
import heapq,json,time,math
import hub_stationary_jet as h
from hub_stationary_contractor import contract
from interval_joint_patch import I,iv,acos,lf,uf
P=Path(__file__).parent;dom=[(lf(I('.379')),uf(I('.37999'))),(lf(acos(I('.38'))/2),uf(acos(I('.375')))),(lf(acos(I('.38'))/2),uf(acos(I('.375')))),(.3,.76),(-.621,.621)];count=0;uid=0;heap=[];closed={'illegal':0,'C862':0,'gradient':0,'curvature':0,'contracted':0,'rootempty':0};start=time.time()
def add(box):
 global count,uid
 count+=1
 old=box;box=contract(box)
 if box is None:closed['rootempty']+=1;return
 if box!=old:closed['contracted']+=1
 x=[I(l,u)for l,u in box];r,b1,b2,v,t=x
 if not h.legal(x):closed['illegal']+=1;return
 # Exact distance between Q1,Q2; high-distance interior maxima excluded by C862.
 dx=r*(iv.sin(2*b1)-iv.sin(2*b2));dy=2*r*(iv.sin(b1)**2+iv.sin(b2)**2)
 if (dx*dx+dy*dy-(I('1.38')*2*r)**2).a>=0:closed['C862']+=1;return
 try:
  g,j=h.enclosure(x)
  if any(y.a>0 or y.b<0 for y in g):closed['gradient']+=1;return
  a,b,c=j[0].d[3],j[0].d[4],j[1].d[4]
  # Any fixed or parameter-dependent direction with strictly positive curvature suffices.
  if a.a>0 or c.a>0 or (a*dx*dx+2*b*dx*dy+c*dy*dy).a>0:
   closed['curvature']+=1;return
 except h.Unsafe:pass
 weights=[10,1,1,2,2];k=max(range(5),key=lambda i:(box[i][1]-box[i][0])*weights[i]);heapq.heappush(heap,(-max((u-l)*w for (l,u),w in zip(box,weights)),uid,box,k));uid+=1
add(dom)
while heap and count<5001:
 _,_,box,k=heapq.heappop(heap);l,u=box[k];m=(l+u)/2
 for a,b in [(l,m),(m,u)]:bb=box.copy();bb[k]=(a,b);add(bb)
 if count%501==0:print(count,len(heap),closed,flush=True)
out={'scope':'bounded diagnostic not theorem unless audited complete','domain':dom,'count':count,'live':len(heap),'closed':closed,'seconds':time.time()-start,'topboxes':[b for _,_,b,k in heapq.nsmallest(10,heap)]};(P/'hub_stationary_contracted_probe.json').write_text(json.dumps(out,indent=2));print(out)
