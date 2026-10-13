import low_low_boundary_jet as f
from all_boundary_derivative import enclosure
from patch_smooth_jet import Unsafe
from interval_joint_patch import I,iv,acos,lf,uf,P
import heapq,time,json,math
heap=[];count=0;uid=0;closed={'illegal':0,'value':0,'nonstationary':0};terminal=-math.inf;start=time.time()
rd=(lf(I('.379')),uf(I('.37999')));bd=(lf(acos(I('.38'))/2),1)
def add(b,j):
 global count,uid,terminal
 count+=1
 try:
  der=enclosure([I(l,h)for l,h in b],j)
  if der.a>0 or der.b<0:closed['nonstationary']+=1;return
 except Unsafe:pass
 res=f.bound([I(l,h)for l,h in b],j)
 if res is None:closed['illegal']+=1;return
 u,ds=res
 if u<28.10695:closed['value']+=1;terminal=max(terminal,u);return
 scale=[10,1,1,.5];k=max(range(4),key=lambda k:(b[k][1]-b[k][0])*scale[k]);priority=max((h-l)*s for (l,h),s in zip(b,scale));heapq.heappush(heap,(-priority,uid,b,j,k,u));uid+=1
for j in range(3):add([rd,bd,bd,(-1,1)if j<2 else(lf(-iv.pi),uf(iv.pi))],j)
while heap and count<6003:
 _,_,b,j,k,_=heapq.heappop(heap);l,h=b[k];m=(l+h)/2
 for ll,hh in [(l,m),(m,h)]:bb=b.copy();bb[k]=(ll,hh);add(bb,j)
 if count%2000==3:print(count,len(heap),closed,time.time()-start,flush=True)
out={'scope':'bothbearings<=1 stationary boundary only; endpoints not covered','count':count,'live':len(heap),'closed':closed,'terminal':terminal,'seconds':time.time()-start,'topboxes':[{'box':b,'branch':j,'upper':u}for _,_,b,j,k,u in heapq.nsmallest(10,heap)]};(P/'low_low_stationary_probe.json').write_text(json.dumps(out,indent=2));print(out)
