"""Bounded full4Douter domain attack; unfinishedbudget returns VALIDLOOSEupper."""
import interval_collapsed_fibers as f
import interval_joint_patch as k
import heapq,json,time,math,hashlib
P=k.P;D=k.acos(k.iv.sqrt(2*(k.I(3)/8)/(1+k.I(3)/8)));dom=k.domain[:3]+[(-k.uf(D),k.uf(D))];heap=[];terminal=-math.inf;uid=0;count=0;start=time.time();target=28.105
# numericaltarget usedonlyworkpruning; everyterminalupper retained.
def add(box):
 global terminal,uid,count
 row=f.bound([k.I(l,h)for l,h in box],tol=.00015,maxeval=31);count+=1
 if row is None:return
 upper=row['upper']
 if upper<=target:terminal=max(terminal,upper)
 else:heapq.heappush(heap,(-upper,uid,box));uid+=1
add(dom)
while heap and count<1601:
 neg,_,box=heapq.heappop(heap)
 # normalizedlargestwidth geometric splitting
 idx=max(range(4),key=lambda i:(box[i][1]-box[i][0])*[5,1,1,1][i]);l,h=box[idx];m=(l+h)/2
 for pair in [(l,m),(m,h)]:bb=box.copy();bb[idx]=pair;add(bb)
 if count%100<3:print('PROGRESS',count,'upper',max(terminal,-heap[0][0]if heap else -math.inf),'seconds',time.time()-start,flush=True)
upper=max(terminal,-heap[0][0]if heap else -math.inf)
out={'scope':'allactualflatpatchescovered by broad4Douter+C849fiber, notsharp','upper':upper,'evaluations':count,'liveboxes':len(heap),'terminal_upper':terminal,'coefficient_sha256':hashlib.sha256(k.frozen.read_bytes()).hexdigest(),'seconds':time.time()-start,'budget_ended':count>=1601,'domain':dom,'source_sha256':{name:hashlib.sha256((P/name).read_bytes()).hexdigest()for name in ['interval_joint_patch.py','interval_patch_delta.py','interval_cancel_fibers.py','interval_collapsed_fibers.py','certify_patch_collapsed_outer.py']},'topboxes':[{'upper':-r[0],'box':r[2]}for r in heapq.nsmallest(5,heap)]}
(P/'patch_outer_collapsed_certificate.json').write_text(json.dumps(out,indent=2));print('DONE',out,flush=True)
