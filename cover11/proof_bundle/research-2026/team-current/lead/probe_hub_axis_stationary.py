"""Test stronger universal 3D statement, omitting norm/bearing constraints."""
from pathlib import Path
import heapq,json,time
import hub_axis_stationary as h
from interval_joint_patch import I
P=Path(__file__).parent;dom=[(.45,1.049),(-.76,.76),(-.535,.535)];heap=[];uid=0;count=0;closed={'distance':0,'gradient':0,'curvature':0};start=time.time()
def add(box):
 global uid,count
 count+=1;d,x,y=[I(l,u)for l,u in box];q1=x*x+(y-d/2)**2;q2=x*x+(y+d/2)**2
 if q1.a>I('.76').b**2 or q2.a>I('.76').b**2:closed['distance']+=1;return
 try:
  f=h.bounds([d,x,y])
  if any(a.a>0 or a.b<0 for a in f[:2]):closed['gradient']+=1;return
  if f[2].a>0:closed['curvature']+=1;return
 except h.Unsafe:pass
 k=max(range(3),key=lambda i:box[i][1]-box[i][0]);heapq.heappush(heap,(-(box[k][1]-box[k][0]),uid,box,k));uid+=1
add(dom)
while heap and count<10001:
 _,_,b,k=heapq.heappop(heap);l,u=b[k];m=(l+u)/2
 for lo,hi in [(l,m),(m,u)]:bb=b.copy();bb[k]=(lo,hi);add(bb)
 if count%1001==0:print(count,len(heap),closed,flush=True)
out={'scope':'universal3Ddiagnostic no theorem','count':count,'live':len(heap),'closed':closed,'seconds':time.time()-start,'domain':dom,'topboxes':[b for _,_,b,k in heapq.nsmallest(10,heap)]};(P/'hub_axis_stationary_probe.json').write_text(json.dumps(out,indent=2));print(out)
