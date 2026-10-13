"""3D stationary exclusion with pole-cleared Newton contractor; budget diagnostic."""
from pathlib import Path
import heapq,json,time,numpy as np
import hub_axis_stationary as h
from interval_joint_patch import I,lf,uf
P=Path(__file__).parent;dom=[(.45,1.049),(-.76,.76),(-.535,.535)];heap=[];uid=0;count=0;closed={'distance':0,'gradient':0,'curvature':0,'rootempty':0,'contracted':0};start=time.time()
# Near either pole Lj<=.005: angular component a_j/Lj>=a_j/.005 dominates
# d/2+othergradient <=1.049/2+c_other+a_other/.445, since 2betaL<c.
assert all((2*b*I('.76')-c).b<0 for b,c in [(h.beta1,h.c1),(h.beta2,h.c2)])
assert (h.a1/I('.005')-I('1.049')/2-h.c2-h.a2/I('.445')).a>0
assert (h.a2/I('.005')-I('1.049')/2-h.c1-h.a1/I('.445')).a>0

def contract(box):
 x=[I(l,u)for l,u in box];mid=[I((l+u)/2)for l,u in box]
 try:
  fm=h.direct(mid);mat=np.array([[float(fm[j].d[i].mid)for i in [1,2]]for j in range(2)]);C=np.linalg.inv(mat)
  if not np.all(np.isfinite(C))or np.max(abs(C))>1e6:return box
  fs=h.direct(x);fc=h.direct(x[:1]+mid[1:]);out=box.copy()
  for i in range(2):
   val=mid[i+1]-sum((I(float(C[i,j]))*fc[j].v for j in range(2)),I(0))
   for k in range(2):val+=(I(int(i==k))-sum((I(float(C[i,j]))*fs[j].d[k+1]for j in range(2)),I(0)))*(x[k+1]-mid[k+1])
   lo=max(box[i+1][0],lf(val));hi=min(box[i+1][1],uf(val))
   if lo>hi:return None
   out[i+1]=(lo,hi)
  return out
 except (h.Unsafe,np.linalg.LinAlgError,ValueError):return box

assert all((2*(h.beta1+h.beta2)-c/I('.43')-a/I('.43')**2).a>0 for c,a in [(h.c1,h.a1),(h.c2,h.a2)])

def add(box):
 global uid,count
 count+=1
 for _ in range(2):
  old=box;box=contract(box)
  if box is None:closed['rootempty']+=1;return
  if box==old:break
  closed['contracted']+=1
 d,x,y=[I(l,u)for l,u in box];q1=x*x+(y-d/2)**2;q2=x*x+(y+d/2)**2
 if q1.a>I('.43').b**2 or q2.a>I('.43').b**2 or q1.b<I('.005').a**2 or q2.b<I('.005').a**2:closed['distance']+=1;return
 try:
  f,js=h.direct_bounds([d,x,y])
  if any(a.a>0 or a.b<0 for a in f[:2]):closed['gradient']+=1;return
  # At a root Jacobian of multiplied gradient equals q1*q2*Hessian.
  if js[0].d[1].a>0 or js[1].d[2].a>0 or (js[0].d[1]+js[1].d[2]).a>0:closed['curvature']+=1;return
 except h.Unsafe:pass
 k=max(range(3),key=lambda i:box[i][1]-box[i][0]);heapq.heappush(heap,(-(box[k][1]-box[k][0]),uid,box,k));uid+=1
add(dom)
while heap and count<10001:
 _,_,b,k=heapq.heappop(heap);l,u=b[k];m=(l+u)/2
 for lo,hi in [(l,m),(m,u)]:bb=b.copy();bb[k]=(lo,hi);add(bb)
 if count%1001==0:print(count,len(heap),closed,flush=True)
out={'scope':'universal3Ddiagnostic no theorem without audit','count':count,'live':len(heap),'closed':closed,'seconds':time.time()-start,'domain':dom,'topboxes':[b for _,_,b,k in heapq.nsmallest(10,heap)]};(P/'axis_radial_probe.json').write_text(json.dumps(out,indent=2));print(out)
