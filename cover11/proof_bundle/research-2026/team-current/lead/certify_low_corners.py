import heapq,time,json,math,hashlib
import low_corner_jet as f
from interval_joint_patch import I,acos,lf,uf,P
count=0;uid=0;heap=[];closed={'illegal':0,'value':0};terminal=-math.inf;start=time.time();dom=[(lf(I('.379')),uf(I('.37999'))),(lf(I('.60946080763725372899')),1),(lf(I('.60946080763725372899')),1)]
def add(b,j,sg):
 global count,uid,terminal
 count+=1;u=f.bound([I(l,h)for l,h in b],j,sg)
 if u is None:closed['illegal']+=1;return
 if u<28.10695:closed['value']+=1;terminal=max(terminal,u);return
 k=max(range(3),key=lambda k:(b[k][1]-b[k][0])*[10,1,1][k]);heapq.heappush(heap,(-(b[k][1]-b[k][0])*[10,1,1][k],uid,b,j,sg,k,u));uid+=1
for j,sg in [(0,-1),(0,1),(1,-1),(1,1),(2,1)]:add(dom,j,sg)
while heap and count<6005:
 _,_,b,j,sg,k,_=heapq.heappop(heap);l,h=b[k];m=(l+h)/2
 for lo,hi in [(l,m),(m,h)]:bb=b.copy();bb[k]=(lo,hi);add(bb,j,sg)
out={'scope':'bothlow normfacecorners andridge diagnostic; coincidentfacecircle separatelycoveredbystationaryarcs','count':count,'live':len(heap),'closed':closed,'terminal':terminal,'seconds':time.time()-start,'domain':dom,'coefficient_sha256':hashlib.sha256((P/'joint_nested_frozen.json').read_bytes()).hexdigest(),'source_sha256':{n:hashlib.sha256((P/n).read_bytes()).hexdigest()for n in ['certify_low_corners.py','low_corner_jet.py','legal_cartesian_value.py','width_endpoint_jet.py','patch_smooth_jet.py','interval_joint_patch.py']},'topboxes':[{'box':b,'j':j,'sign':sg,'upper':u}for _,_,b,j,sg,k,u in heapq.nsmallest(10,heap)]};(P/'low_corners_certificate.json').write_text(json.dumps(out,indent=2));print(out)
