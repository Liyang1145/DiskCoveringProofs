import heapq,json,time,hashlib
from interval_joint_patch import I,pi,P,lf,uf
import face_totalangle_jet as f
from patch_smooth_jet import Unsafe
heap=[];count=0;uid=0;closed={'illegal':0,'value':0};terminal=-float('inf');start=time.time();eps=I('.005');dom=[(lf(I('.379')),uf(I('.37999'))),(lf(I('.60946080763725372899')),1.),(lf(pi/2-eps),uf(pi/2+eps)),(0.,uf(pi/2+eps))]
def add(b,j):
 global count,uid,terminal
 count+=1
 try:u=f.bound([I(l,h)for l,h in b],j)
 except Unsafe:u=float('inf')
 if u is None:closed['illegal']+=1;return
 if u<28.10695:closed['value']+=1;terminal=max(terminal,u);return
 k=max(range(4),key=lambda k:(b[k][1]-b[k][0])*[10,1,1,.5][k]);heapq.heappush(heap,(-(b[k][1]-b[k][0])*[10,1,1,.5][k],uid,b,j,k,u));uid+=1
for j in [0,1]:add(dom,j)
while heap and count<6002:
 _,_,b,j,k,u=heapq.heappop(heap);l,h=b[k];m=(l+h)/2
 for lo,hi in [(l,m),(m,h)]:bb=b.copy();bb[k]=(lo,hi);add(bb,j)
out={'scope':'bothlow entirefacearcs |T-pi/2|<=.005','count':count,'live':len(heap),'closed':closed,'terminal':terminal,'seconds':time.time()-start,'domain':dom,'source_sha256':{n:hashlib.sha256((P/n).read_bytes()).hexdigest()for n in ['certify_coincident_collar.py','face_totalangle_jet.py','width_endpoint_jet.py','patch_smooth_jet.py','interval_joint_patch.py','joint_nested_frozen.json']},'topboxes':[{'box':b,'branch':j,'upper':u}for _,_,b,j,k,u in heapq.nsmallest(10,heap)]};(P/'coincident_collar_certificate.json').write_text(json.dumps(out,indent=2));print(out)
