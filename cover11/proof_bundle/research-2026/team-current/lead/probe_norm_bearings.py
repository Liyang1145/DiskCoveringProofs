import heapq,json,time
from interval_joint_patch import I,pi,P,lf,uf
import norm_bearings_jet as f
from patch_smooth_jet import Unsafe
heap=[];count=0;uid=0;closed={'illegal':0,'value':0};terminal=-float('inf');start=time.time();eps=I('.005');dom=[(lf(I('.379')),uf(I('.37999'))),(lf(I('.60946080763725372899')),1.),(lf(I('.60946080763725372899')),1.),(lf(-pi),uf(pi))]
def add(b):
 global count,uid,terminal
 count+=1
 try:u=f.bound([I(l,h)for l,h in b])
 except Unsafe:u=float('inf')
 if u is None:closed['illegal']+=1;return
 if u<28.10695:closed['value']+=1;terminal=max(terminal,u);return
 k=max(range(4),key=lambda k:(b[k][1]-b[k][0])*[10,1,1,.5][k]);heapq.heappush(heap,(-(b[k][1]-b[k][0])*[10,1,1,.5][k],uid,b,k,u));uid+=1
add(dom)
while heap and count<6001:
 _,_,b,k,u=heapq.heappop(heap);l,h=b[k];m=(l+h)/2
 for lo,hi in [(l,m),(m,h)]:bb=b.copy();bb[k]=(lo,hi);add(bb)
out={'scope':'bothlow normcircle wholebearings, FULLcentralcircle','count':count,'live':len(heap),'closed':closed,'terminal':terminal,'seconds':time.time()-start,'domain':dom,'topboxes':[{'box':b,'upper':u}for _,_,b,k,u in heapq.nsmallest(10,heap)]};(P/'norm_bearings_probe.json').write_text(json.dumps(out,indent=2));print(out)
