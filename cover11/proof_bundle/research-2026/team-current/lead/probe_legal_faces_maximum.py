import heapq,json,time,hashlib
from interval_joint_patch import I,pi,P,lf,uf
import face_legal_arc_maximum as f
from patch_smooth_jet import Unsafe
heap=[];count=0;uid=0;closed={'illegal':0,'value':0};terminal=-float('inf');start=time.time();bd=(lf(I('.60946080763725372899')),1.);dom=[(lf(I('.379')),uf(I('.37999'))),bd,bd,(0.,1.)]
def add(b,key):
 global count,uid,terminal
 count+=1
 try:u=f.bound([I(l,h)for l,h in b],*key)
 except Unsafe:u=float('inf')
 if u is None:closed['illegal']+=1;return
 if u<28.10695:closed['value']+=1;terminal=max(terminal,u);return
 k=max(range(4),key=lambda k:(b[k][1]-b[k][0])*[10,1,1,.5][k]);heapq.heappush(heap,(-(b[k][1]-b[k][0])*[10,1,1,.5][k],uid,b,key,k,u));uid+=1
for j in [0,1]:
 for side in [-1,1]:
  for cut in [0,1]:add(dom,(j,side,cut))
while heap and count<6008:
 _,_,b,key,k,u=heapq.heappop(heap);l,h=b[k];m=(l+h)/2
 for lo,hi in [(l,m),(m,h)]:bb=b.copy();bb[k]=(lo,hi);add(bb,key)
out={'scope':'bothlow entirefacearcs norm+ridge legalchart','count':count,'live':len(heap),'closed':closed,'terminal':terminal,'seconds':time.time()-start,'domain':dom,'source_sha256':{n:hashlib.sha256((P/n).read_bytes()).hexdigest()for n in ['probe_legal_faces_maximum.py','face_legal_arc_maximum.py','face_legal_arc_jet.py','face_normarc_jet.py','legal_cartesian_value.py','width_endpoint_jet.py','patch_smooth_jet.py','interval_joint_patch.py','joint_nested_frozen.json']},'topboxes':[{'box':b,'key':key,'upper':u}for _,_,b,key,k,u in heapq.nsmallest(10,heap)]};(P/'legal_faces_maximum_probe.json').write_text(json.dumps(out,indent=2));print(out)
