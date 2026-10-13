"""C871 all-bearing boundary application; bounded low-bearing objective diagnostic."""
import interval_hub_saturated as base
import interval_patch_delta as fibers
from interval_joint_patch import I,iv,acos,lf,uf,P
import heapq,json,time,math

def bound(box):
 st=base.setup([I(l,u)for l,u in box])
 if st is None:return None
 K,ws,cs=st;ww=[fibers.envelope(f,dom,.0002,65)for f,dom in ws];cc=[fibers.envelope(f,dom,.0002,65)for f,dom in cs]
 if any(a['upper']==-math.inf for a in ww)or all(a['upper']==-math.inf for a in cc):return None
 return {'upper':uf(K+sum((I(a['upper'])for a in ww),I(0))+I(max(a['upper']for a in cc))),'widths':ww,'circles':cc}
if __name__=='__main__':
 start=time.time();heap=[];uid=0;count=0;terminal=-math.inf
 rdom=(lf(I('.379')),uf(I('.37999')));blo=lf(acos(I('.38'))/2);bhi=uf(acos(I('.379')));domains=[[rdom,(blo,1),(blo,bhi)],[rdom,(1,bhi),(blo,1)]]
 def add(box):
  global uid,count,terminal
  a=bound(box);count+=1
  if a is None:return
  if a['upper']<28.1069:terminal=max(terminal,a['upper']);return
  heapq.heappush(heap,(-a['upper'],uid,box,a));uid+=1
 for dom in domains:add(dom)
 while heap and count<122:
  _,_,box,_=heapq.heappop(heap);k=max(range(3),key=lambda i:(box[i][1]-box[i][0])*[5,1,1][i]);l,u=box[k];m=(l+u)/2
  for a,b in [(l,m),(m,u)]:bb=box.copy();bb[k]=(a,b);add(bb)
  if count%20==2:print(count,'live',len(heap),'upper',-heap[0][0]if heap else terminal,'seconds',time.time()-start,flush=True)
 out={'scope':'C871 lowbearing boundary objective diagnostic; unfinished is not exclusion','count':count,'live':len(heap),'upper':max(terminal,-heap[0][0]if heap else -math.inf),'seconds':time.time()-start,'domains':domains,'topboxes':[{'box':b,'upper':-v,'circle_uppers':[c['upper']for c in a['circles']],'width_uppers':[c['upper']for c in a['widths']]}for v,_,b,a in heapq.nsmallest(8,heap)]};(P/'lowbearing_boundary_probe.json').write_text(json.dumps(out,indent=2));print(out)
