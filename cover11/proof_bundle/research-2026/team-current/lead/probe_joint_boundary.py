"""Bounded experiment for coupled six-variable boundary MVT, all low bearings."""
import heapq,json,time,math
import joint_boundary_jet as f
from interval_joint_patch import I,iv,acos,asin,g,lf,uf,P
start=time.time();heap=[];uid=0;count=0;terminal=-math.inf;closed=0
rdom=(lf(I('.379')),uf(I('.37999')));blo=lf(acos(I('.38'))/2);bhi=uf(acos(I('.379')));wd=(lf(g),uf(2*asin(I('.38'))));domains=[]
for b1,b2 in [((blo,1),(blo,bhi)),((1,bhi),(blo,1))]:
 for j in range(3):domains.append(([rdom,b1,b2,(-bhi,bhi)if j<2 else(lf(-iv.pi),uf(iv.pi)),wd,wd],j))
def add(box,j):
 global count,uid,terminal,closed
 count+=1;a=f.bound([I(l,u)for l,u in box],j)
 if a is None:closed+=1;return
 up,der=a
 if up<28.10695:closed+=1;terminal=max(terminal,up);return
 # prioritize normalized size, avoiding broad singular infinity starving remainder
 scale=[10,1,1,.3,1,1];k=max(range(6),key=lambda k:(box[k][1]-box[k][0])*scale[k])
 priority=max((u-l)*w for (l,u),w in zip(box,scale))
 heapq.heappush(heap,(-priority,uid,box,j,k,up));uid+=1
for b,j in domains:add(b,j)
while heap and count<3006:
 _,_,b,j,k,_=heapq.heappop(heap);l,u=b[k];m=(l+u)/2
 for lo,hi in [(l,m),(m,u)]:bb=b.copy();bb[k]=(lo,hi);add(bb,j)
 if count%500==6:print(count,len(heap),closed,time.time()-start,flush=True)
out={'scope':'6Dcoupled lowbearingboundary diagnostic, no theorem','count':count,'live':len(heap),'closed':closed,'terminal':terminal,'seconds':time.time()-start,'topboxes':[{'box':b,'branch':j,'upper':up}for _,_,b,j,k,up in heapq.nsmallest(10,heap)]};(P/'joint_boundary_probe.json').write_text(json.dumps(out,indent=2));print(out)
