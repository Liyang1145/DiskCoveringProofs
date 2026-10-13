"""Edge-disjointfacepack certificate, intervalboxtrees; no area deficitdoublecounting."""
from face_deficit_certificate import *
def certify_pack(q,edges,faces,row,pack,budget=6000):
 t=list(map(Q,row['rational_angles']));y=list(map(Q,row['rational_potentials']));nu=Q(row['rational_nu']);lam=Q(row['rational_lambda']);base=verify(q,edges,t,y,nu,lam);used=set();data=[];uid=0
 for face in pack:
  ee=[tuple(sorted(e))for e in combinations(faces[face],2)];assert not used.intersection(ee);used.update(ee);assert all(sum(all(v in f for v in e)for f in faces)==2 for e in ee);p=[sum(y[v]for v in e)for e in ee];base-=sum((edgeold(t[q+edges.index(e)],pp)for e,pp in zip(ee,p)),I(0));opts=[0 if float(v)>=float(U*U)else(math.pi if float(v)<=-float(U*U)else math.acos(float(v/(U*U))))for v in p];box=[(Q(0),Q(1))]*3;b=boxbound(box,p,opts);data.append((face,p,opts,[(-b.hi,0,box)]))
 for k in range(budget):
  upper=base.hi-sum(d[3][0][0]for d in data)
  if upper<0:break
  face,p,opts,heap=data[k%len(data)];neg,_,box=heapq.heappop(heap);j=max(range(3),key=lambda j:box[j][1]-box[j][0]);lo,hi=box[j];mid=(lo+hi)/2
  for seg in[(lo,mid),(mid,hi)]:
   b=box.copy();b[j]=seg;uid+=1;v=boxbound(b,p,opts);heapq.heappush(heap,(-v.hi,uid,b))
 upper=base.hi-sum(d[3][0][0]for d in data)
 return {'family':row['family'],'index':row['index'],'status':'excluded'if upper<0 else'inconclusive','upper_display':upper/S,'upper_exact':str(Q(upper,S)),'parts':[{'face':f,'leaves':[[[str(a),str(b)]for a,b in box]for neg,uid,box in heap]}for f,p,o,heap in data]}
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());rows={(x['family'],x['index']):x for x in[json.loads(x)for x in(P/'joint-innernorm-catalogue.jsonl').read_text().splitlines()]};probes=json.loads((P/'face-pack-probe.json').read_text())['runs'];out=[];start=time.time()
 for test in probes:
  if test['numeric_new_upper']>=0:continue
  fam=test['family'];idx=test['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});rec=certify_pack(q,edges,faces,rows[fam,idx],test['faces']);out.append(rec);print(fam,idx,rec['status'],rec['upper_display'],'leaves',sum(len(x['leaves'])for x in rec['parts']),'seconds',time.time()-start,flush=True)
 (P/'face-pack-certificate.json').write_text(json.dumps({'status':'interval_bounds_edgedisjointpacks','runs':out},indent=2))
