import coupled_bearing_envelope as f
from interval_joint_patch import I,iv,acos,lf,uf,P
import heapq,time,json,math
start=time.time();heap=[];count=0;uid=0;closed=0;terminal=-math.inf
rd=(lf(I('.379')),uf(I('.37999')));lo=lf(acos(I('.38'))/2);hi=uf(acos(I('.379')))
def add(b,j):
 global count,uid,closed,terminal
 count+=1;u=f.bound([I(l,h)for l,h in b],j,17)
 if u is None:closed+=1;return
 if u<28.10695:closed+=1;terminal=max(terminal,u);return
 k=max(range(4),key=lambda k:(b[k][1]-b[k][0])*[10,1,1,.5][k]);prio=max((h-l)*w for (l,h),w in zip(b,[10,1,1,.5]))
 heapq.heappush(heap,(-prio,uid,b,j,k,u));uid+=1
for b1,b2 in [((lo,1),(lo,hi)),((1,hi),(lo,1))]:
 for j in range(3):add([rd,b1,b2,(-hi,hi)if j<2 else(lf(-iv.pi),uf(iv.pi))],j)
while heap and count<1506:
 _,_,b,j,k,_=heapq.heappop(heap);l,h=b[k];m=(l+h)/2
 for ll,hh in [(l,m),(m,h)]:bb=b.copy();bb[k]=(ll,hh);add(bb,j)
 if count%200==6:print(count,len(heap),closed,time.time()-start,flush=True)
out={'scope':'coupled bearing envelope diagnostic','count':count,'live':len(heap),'closed':closed,'terminal':terminal,'seconds':time.time()-start,'topboxes':[{'box':b,'branch':j,'upper':u}for _,_,b,j,k,u in heapq.nsmallest(10,heap)]};(P/'coupled_bearing_envelope_probe.json').write_text(json.dumps(out,indent=2));print(out)
