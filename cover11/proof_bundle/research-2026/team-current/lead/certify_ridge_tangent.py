"""Bounded interval component enclosure for exact ridge tangent split; result may remain loose."""
import ridge_tangent_jet as f
from interval_joint_patch import I,iv,g,asin,R,uf,lf
from pathlib import Path
import math,json,heapq,time,hashlib
P=Path(__file__).parent
# Outward cover actual assembly radius interval, all high bearings, all legal widths.
dom=[(lf(I('.379')),uf(I('.37999'))),(1.,1.1863995522992576),(lf(g),uf(2*asin(R)))]
start=time.time();out=[]
for j in [0,1]:
 heap=[];uid=0;count=0;terminal=-math.inf
 # Target only work threshold; every terminal upper retained.
 target=[-.04782,-.04684][j]
 def add(box):
  global uid,count,terminal
  count+=1;res=f.bound([I(a,b)for a,b in box],j)
  if res is None:return
  up,der=res
  if up<=target:terminal=max(terminal,up);return
  k=max(range(3),key=lambda i:(box[i][1]-box[i][0])*der[i])
  heapq.heappush(heap,(-up,uid,box,k));uid+=1
 add(dom.copy())
 while heap and count<5001:
  _,_,box,k=heapq.heappop(heap);lo,hi=box[k];m=(lo+hi)/2
  for pair in [(lo,m),(m,hi)]:y=box.copy();y[k]=pair;add(y)
 up=max(terminal,-heap[0][0]if heap else -math.inf)
 out.append({'j':j,'upper':up,'count':count,'live':len(heap),'terminal':terminal,'worst':[{'box':t[2],'upper':-t[0]}for t in heapq.nsmallest(3,heap)]});print('component',j,up,count,len(heap),flush=True)
const=f.constant(I(*dom[0]));total=uf(const+sum((I(x['upper'])for x in out),I(0)))
res={'scope':'HIGHBEARING RIDGE ONLY; fixed tangent tau87/40; actualr.379-.37999; no endpointreduction','domain':dom,'components':out,'constant':str(const),'upper':total,'seconds':time.time()-start,'coefficient_sha256':hashlib.sha256((P/'joint_nested_frozen.json').read_bytes()).hexdigest(),'source_sha256':{x:hashlib.sha256((P/x).read_bytes()).hexdigest()for x in ['ridge_tangent_jet.py','certify_ridge_tangent.py','patch_smooth_jet.py','interval_joint_patch.py']}}
(P/'ridge_tangent_certificate.json').write_text(json.dumps(res,indent=2));print('DONE',res,flush=True)
