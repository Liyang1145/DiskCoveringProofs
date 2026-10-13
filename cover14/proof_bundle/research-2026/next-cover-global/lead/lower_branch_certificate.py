"""Edge-disjointfacepack certificate, intervalboxtrees; no area deficitdoublecounting."""
from lower_branch_box_kernel import *
def certify_pack(q,edges,faces,row,pack,budget=6000):
 t=list(map(Q,row['rational_angles']));y=list(map(Q,row['rational_potentials']));nu=Q(row['rational_nu']);lam=Q(row['rational_lambda']);base=verify(q,edges,t,y,nu,lam);used=set();data=[];uid=0
 for face in pack:
  ee=[tuple(sorted(e))for e in combinations(faces[face],2)];assert not used.intersection(ee);used.update(ee);assert all(sum(all(v in f for v in e)for f in faces)in (1,2) for e in ee);p=[sum(y[v]for v in e)for e in ee];base-=sum((edgeold(t[q+edges.index(e)],pp)for e,pp in zip(ee,p)),I(0));opts=[0 if float(v)>=float(U*U)else(math.pi if float(v)<=-float(U*U)else math.acos(float(v/(U*U))))for v in p];box=[(Q(0),Q(1))]*3;b=boxbound(box,p,opts);data.append((face,p,opts,[(-b.hi,0,box)]))
 for k in range(budget):
  upper=base.hi-sum(d[3][0][0]for d in data)
  if upper<0:break
  face,p,opts,heap=data[k%len(data)];neg,_,box=heapq.heappop(heap);j=max(range(3),key=lambda j:box[j][1]-box[j][0]);lo,hi=box[j];mid=(lo+hi)/2
  for seg in[(lo,mid),(mid,hi)]:
   b=box.copy();b[j]=seg;uid+=1;v=boxbound(b,p,opts);heapq.heappush(heap,(-v.hi,uid,b))
 upper=base.hi-sum(d[3][0][0]for d in data)
 return {'family':row['family'],'index':row['index'],'status':'excluded'if upper<0 else'inconclusive','upper_display':upper/S,'upper_exact':str(Q(upper,S)),'parts':[{'face':f,'leaves':[[[str(a),str(b)]for a,b in box]for neg,uid,box in heap]}for f,p,o,heap in data]}

