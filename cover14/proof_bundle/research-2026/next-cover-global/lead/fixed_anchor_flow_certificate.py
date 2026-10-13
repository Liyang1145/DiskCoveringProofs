"""Exact tree-flow repair + Fraction bound for rational angular boxes (not sourcefloat anchorclaims)."""
import json,math,hashlib
from pathlib import Path
from fractions import Fraction as F
from collections import deque
from shared_radius_corner_fraction_kernel import sc
P=Path(__file__).resolve().parent

def norm_upper(v,digits=40):
 a=sum(x*x for x in v);S=10**digits;k=math.isqrt((a.numerator*S*S)//a.denominator);q=F(k,S)
 if q*q<a:q+=F(1,S)
 assert q*q>=a
 return q

def certify(row,epsilon):
 D=row['incidence_matrix'];m=len(D);nv=len(D[0]);root=nv;z=[[F(format(v,'.14f'))for v in p]for p in row['flow_vectors']];adj=[[]for j in range(nv+1)];ends=[]
 for e,dr in enumerate(D):
  u=dr.index(1);v=dr.index(-1)if -1 in dr else root;ends.append((u,v));adj[u].append((v,e));adj[v].append((u,e))
 parent={root:None};order=[root]
 for u in order:
  for v,e in adj[u]:
   if v not in parent:parent[v]=(u,e);order.append(v)
 assert len(order)==nv+1
 balance=[[sum(F(D[e][u])*z[e][k]for e in range(m))for k in range(2)]for u in range(nv)]
 for u in reversed(order[1:]):
  v,e=parent[u];sign=D[e][u];correction=[-x/sign for x in balance[u]]
  for k in range(2):
   z[e][k]+=correction[k]
   if v!=root:balance[v][k]+=D[e][v]*correction[k]
   balance[u][k]=F(0)
 assert all(sum(F(D[e][u])*z[e][k]for e in range(m))==0 for u in range(nv)for k in range(2))
 nf=len(row['faces']);q=len(row['anchors']);assert m==3*nf+2*q
 b=[[sum((z[3*nf+2*j+h][k]for h in range(2)),F(0))for k in range(2)]for j in range(q)]
 theta=[F(format(math.atan2(p[1],p[0]),'.14f'))for p in row['anchors']];num=F(0);lipschitz=F(0)
 for t,bb in zip(theta,b):
  sn,cs=sc(abs(t))
  if t<0:sn=(-sn[1],-sn[0])
  for val,iv in zip(bb,[cs,sn]):num+=min(-val*iv[0],-val*iv[1])
  lipschitz+=norm_upper(bb)
 den=sum((norm_upper(v)for v in z),F(0));lower=(num-epsilon*lipschitz)/den;U=F('.33173203427623414')
 return {'status':'exact_balanced_flow_angular_box_bound','case':row['case'],'angle_center_radians':list(map(str,theta)),'epsilon_radians':str(epsilon),'lower_radius_exact':str(lower),'lower_radius_display':float(lower),'excludes_radius_U':lower>U,'norm_denominator_upper':str(den),'center_numerator_lower':str(num),'angular_lipschitz_upper':str(lipschitz),'flow_vectors':[[str(v)for v in p]for p in z],'incidence_matrix':D,'faces':row['faces'],'owners':row['owners'],'scope':'all anchors in the stated independent rational-angle boxes; validity for arbitrary anglebox data as SOCP lowerbound, cover implication requires ordered-one-winding anchors'}
if __name__=='__main__':
 src=P/'fixed-anchor-convex-probe.json';rows=json.loads(src.read_text())['runs'];out=[certify(r,F('0.0000000001')if r['case']=='candidate'else F('0.001'))for r in rows];assert not out[0]['excludes_radius_U'] and out[1]['excludes_radius_U'];(P/'fixed-anchor-flow-certificate.json').write_text(json.dumps({'status':'exact_rational_flow_bounds','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'runs':out},indent=2));print([{k:r[k]for k in ['case','epsilon_radians','lower_radius_display','excludes_radius_U']}for r in out])
