"""Bounded stationary-value exclusion. CONDITIONAL on C861, C863 and ridge bound for endpoints.
No all-face certificate if live boxes remain. Second-order Cartesian AD independent of hand kernels.
"""
from pathlib import Path
import math,json,heapq,time
import face_second_jet as f
import face_derivative_outer_jet as outer
from patch_smooth_jet import Unsafe as OuterUnsafe
from interval_hub_boundary import setup
import interval_patch_delta as fibers
from interval_joint_patch import I,uf,lf
P=Path(__file__).parent;dom=[(lf(I('.379')),uf(I('.37999'))),(1.,1.1863995522992576),(1.,1.1863995522992576),(-1.1863995522992576,1.1863995522992576)];heap=[];count=0;uid=0;closed={'illegal':0,'nonstationary':0,'positivecurvature':0,'value':0};start=time.time();target=28.10695;terminal=-math.inf;cache={}
def add(box,j):
 global count,uid,terminal
 count+=1;x=[I(l,h)for l,h in box]
 if not f.legal(x,j):closed['illegal']+=1;return
 try:
  gp,ggrad=outer.enclosure(x,j)
  if gp.a>0 or gp.b<0:closed['nonstationary']+=1;return
 except OuterUnsafe:pass
 try:a=f.saturated(x,j)
 except f.Unsafe:a=None
 if a is not None:
  try:
   mid=x.copy();mid[3]=I((box[3][0]+box[3][1])/2);am=f.saturated(mid,j)
   tight=am.d+a.h*(x[3]-mid[3]);a.d=I(max(a.d.a,tight.a),min(a.d.b,tight.b))
   # Stationary-point-only Taylor expansion about the unknown stationary point.
   # f(mid)=f(d)+.5 f''(xi)(mid-d)^2; no f' term atstationaryd.
   centered=am.v-a.h*((x[3]-mid[3])**2)/2
   if max(a.v.a,centered.a)>min(a.v.b,centered.b):closed['nonstationary']+=1;return
   a.v=I(max(a.v.a,centered.a),min(a.v.b,centered.b))
  except f.Unsafe:pass
  if a.d.a>0 or a.d.b<0:closed['nonstationary']+=1;return
  if a.h.a>0:closed['positivecurvature']+=1;return
 up=math.inf
 if a is not None and max(h-l for l,h in box[1:3])<.05:
  key=tuple(box[:3])
  if key not in cache:
   st=setup(x[:3])
   if st is None:cache[key]=None
   else:
    K,ws,_=st;wv=[fibers.envelope(fun,d,.0002,65)for fun,d in ws]
    cache[key]=None if any(w['upper']==-math.inf for w in wv)else K+sum((I(w['upper'])for w in wv),I(0))
  if cache[key] is None:closed['illegal']+=1;return
  up=uf(cache[key]+a.v)
  if up<target:closed['value']+=1;terminal=max(terminal,up);return
 k=max(range(4),key=lambda k:(box[k][1]-box[k][0])*[10,1,1,.5][k])
 heapq.heappush(heap,(-max((h-l)*w for (l,h),w in zip(box,[10,1,1,.5])),uid,box,j,k,up));uid+=1
for j in [0,1]:add(dom.copy(),j)
while heap and count<16002:
 _,_,box,j,k,_=heapq.heappop(heap);lo,hi=box[k];m=(lo+hi)/2
 for sub in [(lo,m),(m,hi)]:bb=box.copy();bb[k]=sub;add(bb,j)
 if count%500==0:print(count,len(heap),closed,time.time()-start,flush=True)
out={'scope':'CONDITIONAL stationaryvalueonly; budgetdiagnostic','domain':dom,'count':count,'live':len(heap),'closed':closed,'terminal':terminal,'seconds':time.time()-start,'topboxes':[{'box':b,'j':j,'upper':u}for _,_,b,j,k,u in heapq.nsmallest(10,heap)]}
(P/'stationary_face_bound_probe.json').write_text(json.dumps(out,indent=2));print(out)
