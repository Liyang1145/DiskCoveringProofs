"""Different arithmetic and construction: rebuild incidence and validate saved balancedflows."""
from area_safe_certificate import I,Q,S,PI,trig,P,U
import json,hashlib
def normiv(p):
 a=sum(v*v for v in p)
 return I(0) if a==0 else I(a).sqrt()
src=P/'fixed-anchor-flow-certificate.json';rows=json.loads(src.read_text())['runs'];out=[]
for row in rows:
 faces=row['faces'];owners=row['owners'];n=14;nf=len(faces);nv=n+nf;q=len(owners);inc=[];aid=[]
 for f,vs in enumerate(faces):
  for v in vs:
   d=[0]*nv;d[v]=1;d[n+f]=-1;inc.append(d);aid.append(None)
 for j,vs in enumerate(owners):
  for v in vs:
   d=[0]*nv;d[v]=1;inc.append(d);aid.append(j)
 assert inc==row['incidence_matrix'];z=[list(map(Q,p))for p in row['flow_vectors']];assert len(z)==len(inc)
 assert all(sum(inc[e][u]*z[e][k]for e in range(len(inc)))==0 for u in range(nv)for k in range(2))
 if row['case']=='q11-58':
  assert faces==json.loads((P/'q11-pocket-catalogue.json').read_text())['entries'][58]['faces'];assert owners==[[i,(i+1)%11]for i in range(11)]
 else:
  G=json.loads((P/'stress-barycentric-result.json').read_text());assert faces==[f['ids']for f in G['faces']]+[[4,6,12],[5,7,13]];assert owners==[a['owners']for a in G['anchors']]
 b=[[sum((z[e][k]for e,jj in enumerate(aid)if jj==j),Q(0))for k in range(2)]for j in range(q)];den=sum((normiv(p)for p in z),I(0));lip=sum((normiv(p)for p in b),I(0));num=I(0);angles=list(map(Q,row['angle_center_radians']));eps=Q(row['epsilon_radians'])
 for t,bb in zip(angles,b):
  sn,cs=trig(I(t));num-=I(bb[0])*cs+I(bb[1])*sn
 lower=(num-I(eps)*lip)/den;assert (lower.lo> I(U).hi)==row['excludes_radius_U']
 # One cyclic winding in owner order for q11 calibration; eachbox remains legal.
 ordered=True
 if row['case']=='q11-58':
  for i,t in enumerate(angles):
   gap=I(angles[(i+1)%q]-t)
   if gap.hi<0:gap+=2*PI
   assert gap.lo-2*I(eps).hi>0 and gap.hi+2*I(eps).hi<PI.lo
 out.append({'case':row['case'],'status':'integer_interval_flow_replay','lower_radius_exact':str(Q(lower.lo,S)),'lower_radius_display':lower.lo/S,'excludes_U':lower.lo>I(U).hi,'incidence_rebuilt':True,'exact_balance_checked':True,'q11_angle_boxes_order_checked':ordered})
(P/'fixed-anchor-flow-replay.json').write_text(json.dumps({'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'runs':out},indent=2));print(out)
