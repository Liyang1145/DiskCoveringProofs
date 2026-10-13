"""Bounded7Djoint centered proof-kernel attack, preserve constraints and fullobjectivegradient."""
import patch_smooth_jet as sj
import interval_patch_delta as fibers
import interval_joint_patch as k
import heapq,json,math,time,hashlib
P=k.P;start=time.time();files=['patch_smooth_jet.py','interval_joint_patch.py','interval_patch_delta.py','certify_patch_jet.py'];hashes={f:hashlib.sha256((P/f).read_bytes()).hexdigest()for f in files}
D=k.acos(k.iv.sqrt(k.I(6)/11));dom=k.domain[:3]+[(-k.uf(D),k.uf(D))]+k.domain[4:];heap=[];count=0;uid=0;adok=0;terminal=-math.inf
# Physicalboxes, no nonrigorouspruning.
def add(box):
 global count,uid,adok,terminal
 count+=1;ib=[k.I(l,h)for l,h in box];st=fibers.setup(ib[:4])
 if st is None:return
 _,fs=st
 for i,(_,d)in enumerate(fs,4):
  l=max(box[i][0],d[0]);h=min(box[i][1],d[1])
  if l>h:return
  box[i]=(l,h);ib[i]=k.I(l,h)
 r,b1,b2,de,w1,w3,H=ib;A=b1-de
 v=k.evaluate([r,b1,b2,A,w1,w3,H])
 if v is None:return
 upper=k.uf(v);weights=[(h-l)*a for (l,h),a in zip(box,[5,1,1,1,1,1,1])]
 try:
  au,jet,mb=sj.mean_bound(ib);upper=min(upper,au);adok+=1
  weights=[k.uf(abs(d))*(h-l)for d,(l,h)in zip(jet.d,box)]
 except sj.Unsafe:pass
 if upper<28.105:terminal=max(terminal,upper);return
 idx=max(range(7),key=lambda i:weights[i]);heapq.heappush(heap,(-upper,uid,box,idx));uid+=1
add(dom.copy())
while heap and count<2001:
 neg,_,box,i=heapq.heappop(heap);l,h=box[i];m=(l+h)/2
 if m==l or m==h:terminal=max(terminal,-neg);continue
 for sub in [(l,m),(m,h)]:bb=box.copy();bb[i]=sub;add(bb)
 if count%400<3:print(count,'upper',max(terminal,-heap[0][0]if heap else -math.inf),'adok',adok,'seconds',time.time()-start,flush=True)
out={'upper':max(terminal,-heap[0][0]if heap else -math.inf),'evaluations':count,'adok':adok,'seconds':time.time()-start,'liveboxes':len(heap),'terminal_upper':terminal,'source_sha256':hashes,'coefficient_sha256':hashlib.sha256(k.frozen.read_bytes()).hexdigest(),'scope':'necessaryactualflatpatch, all7Dbroadboxes; loosebudgetupper','topboxes':[{'upper':-a,'box':b,'split':i}for a,_,b,i in heapq.nsmallest(3,heap)]};(P/'patch_jet_budget.json').write_text(json.dumps(out,indent=2));print(out,flush=True)
