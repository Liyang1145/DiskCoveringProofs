"""Independent Fraction replay for all-face factor dual, including exact dyadic partition audit."""
from shared_radius_corner_fraction_kernel import *

def check_partition(boxes):
 # Each production splitbisects longestside, tieslowestindex. Reconstructaddresses independently.
 assert all(F(0)<=a<b<=F(1)for box in boxes for a,b in box)
 assert sum((math.prod(b-a for a,b in box)for box in boxes),F(0))==1
 root={}
 for target in boxes:
  cur=[(F(0),F(1))]*3;node=root
  while cur!=target:
   assert 'leaf'not in node
   j=max(range(3),key=lambda j:cur[j][1]-cur[j][0]);a,b=cur[j];m=(a+b)/2
   if target[j][1]<=m:bit=0;cur[j]=(a,m)
   else:assert target[j][0]>=m;bit=1;cur[j]=(m,b)
   node=node.setdefault(bit,{})
  assert not node;node['leaf']=True
 # prefixfree dyadicbox addresses imply disjointinteriors; sumvolume1 coverscube up toboundaries.

def facebound(box,p):
 if sum(l for l,h in box)>2:return point(F(-10**9))
 lo=[v[0]for v in box];hi=[v[1]for v in box];dist=mul(pi,point(max(F(0),sum(lo)-1,1-sum(hi))));pen=mul(point(U*U/2),mul(sub(point(F(1)),cosiv(mul(pi,point(min(lo))))),dist));b=point(F(0))
 for(a,c),pp in zip(box,p):b=add(b,sup(a,c,pp))
 old=sub(b,pen);X=radius_upper(box)
 if X<1:
  val=point(F(0))
  for(a,c),pp in zip(box,p):val=add(val,scaled_sup(a,c,pp,X))
  old=(min(old[0],val[0]),min(old[1],val[1]))
 if sum(hi)<1 and sum(lo)+min(lo)>=1 and min(lo)>0:
  d=(1-sum(hi))/2;sd=max(F(0),sinpoint(d)[0]);values=[]
  for l,h in box:values.append(2*U*U*max(F(0),min(sinpoint(l)[0],sinpoint(h)[0]))*max(F(0),sinpoint(l/2)[0])*sd)
  lower=min(values);old=(min(old[0],b[0]-1),min(old[1],b[1]-lower))
 return old

def verify_all(q,edges,faces,row,cert):
 y=list(map(F,row['rational_potentials']));w=list(map(F,row['rational_face_weights']));pp=[list(map(F,rr))for rr in row['rational_face_potentials']];assert len(w)==len(faces)==len(pp)and all(x>=0 for x in w)and all(len(x)==3 for x in pp);ee=[[tuple(sorted(e))for e in combinations(f,2)]for f in faces];base=replay(q,[],row)
 for u,v in edges:
  inc=[(f,ee[f].index((u,v)))for f in range(len(faces))if (u,v)in ee[f]];assert len(inc)in(1,2);c=1-sum(w[f]for f,j in inc);assert c>=0;p=y[u]+y[v]-sum(pp[f][j]for f,j in inc)
  if c==0:base=add(base,mul(pi,point(max(F(0),-p))))
  else:base=rnd(add(base,scaled_sup(F(0),F(1),p,c)))
 parts={z['face']:z for z in cert['parts']};assert len(parts)==len(cert['parts'])and set(parts)=={f for f in range(len(faces))if w[f]>0}
 for f in range(len(faces)):
  if w[f]==0:base=add(base,mul(pi,point(sum(max(F(0),-p)for p in pp[f]))));continue
  p=[v/w[f]for v in pp[f]];boxes=[[(F(a),F(b))for a,b in box]for box in parts[f]['leaves']];check_partition(boxes);bounds=[facebound(box,p)for box in boxes];base=rnd(add(base,mul(point(w[f]),vmax(bounds))))
 return base
if __name__=='__main__':
 D10=json.loads((P/'k10-catalogue-corrected.json').read_text());D11=json.loads((P/'q11-pocket-catalogue.json').read_text());data=json.loads((P/'all-face-consistency-certificate.json').read_text())['runs'];out=[];start=time.time()
 # partitioncontrol validcomplete cube, then overlapping/gap arrangement rejection.
 check_partition([[(F(0),F(1,2)),(F(0),F(1)),(F(0),F(1))],[(F(1,2),F(1)),(F(0),F(1)),(F(0),F(1))]])
 try:check_partition([[(F(0),F(1,2)),(F(0),F(1)),(F(0),F(1))]]*2)
 except AssertionError:pass
 else:raise AssertionError('overlapcontrol not rejected')
 for rec in data:
  row=rec['row'];cert=rec['certificate']
  if cert['status']!='excluded':continue
  fam=row['family'];idx=row['index'];q=int(fam.split('/')[0]);faces=D11['entries'][idx]['faces']if q==11 else D10[fam][idx]['faces'];edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});bound=verify_all(q,edges,faces,row,cert);assert bound[1]<0;out.append({'family':fam,'index':idx,'upper_exact':str(bound[1]),'upper_display':float(bound[1])});print('replayed',fam,idx,float(bound[1]),'seconds',time.time()-start,flush=True);sc.cache_clear()
 (P/'all-face-consistency-fraction-replay.json').write_text(json.dumps({'status':'independent_fraction_replay_all_factor_duals','runs':out},indent=2));print('DONE',len(out),flush=True)
