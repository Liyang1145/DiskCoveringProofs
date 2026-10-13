"""LocalboxQ0 ONLY; provenH/deltaelimination used. Widthsglobalfibersstillcovered."""
import patch_ridge_jet as j
import interval_cancel_fibers as f
import interval_joint_patch as k
import heapq,json,math,time,hashlib
P=k.P;dom=[(k.lf(k.I(a)),k.uf(k.I(b)))for a,b in [(".379",".38"),("1.106","1.108"),("1.068","1.071")]]+[(k.lf(k.g),k.uf(2*k.asin(k.R))),(k.lf(k.g),k.uf(2*k.asin(k.R)))];heap=[];count=0;uid=0;terminal=-math.inf;start=time.time()
def add(box):
 global count,uid,terminal
 count+=1;r,b1,b2,w1,w3=[k.I(l,h)for l,h in box];de=b1-b2;st=f.setup([r,b1,b2,de])
 if st is None:return
 for i in [3,4]:
  l=max(box[i][0],st[1][i-3][1][0]);h=min(box[i][1],st[1][i-3][1][1])
  if l>h:return
  box[i]=(l,h)
 ib=[k.I(l,h)for l,h in box];r,b1,b2,w1,w3=ib;H=2*r*k.iv.sin(b1+b2);de=b1-b2;seven=[r,b1,b2,de,w1,w3,H]
 # Localjetangular continuation isunsafeonwidewidths; usecancelnatural fallback
 K,fs=st;wv=[fun(w)for (fun,_),w in zip(fs,[w1,w3,H])]
 if any(v is None for v in wv):return
 up=k.uf(K+sum(wv,k.I(0)));weights=[(h-l)*a for (l,h),a in zip(box,[2,1,1,1,1])]
 try:
  au,jet,_=j.mean_bound(seven);up=min(up,au);weights=[k.uf(abs(jet.d[t]))*(h-l)for t,(l,h)in zip([0,1,2,4,5],box)]
 except j.Unsafe:pass
 if up<28.1044:terminal=max(terminal,up);return
 split=max(range(5),key=lambda i:weights[i]);heapq.heappush(heap,(-up,uid,box,split));uid+=1
add(dom.copy())
while heap and count<2001:
 neg,_,box,i=heapq.heappop(heap);l,h=box[i];m=(l+h)/2
 for sub in [(l,m),(m,h)]:bb=box.copy();bb[i]=sub;add(bb)
 if count%400<3:print(count,max(terminal,-heap[0][0]if heap else -math.inf),time.time()-start,flush=True)
out={'scope':'LOCAL Q0 r.379-.38,b1 1.106-1.108,b2 1.068-1.071,delta .035-.040, allHwidthfibers; usingprovedridgeelimination','upper':max(terminal,-heap[0][0]if heap else -math.inf),'evaluations':count,'liveboxes':len(heap),'terminal_upper':terminal,'seconds':time.time()-start,'coefficient_sha256':hashlib.sha256(k.frozen.read_bytes()).hexdigest()};(P/'local_ridge_upper.json').write_text(json.dumps(out,indent=2));print(out)
