"""Symmetry averaged exactbalancedrational flow + Xdiameterflows. Numericreferencealignment only."""
import json,math,heapq
from pathlib import Path
from fractions import Fraction as F
import numpy as np
P=Path(__file__).resolve().parent;a=json.loads((P/'fixed-anchor-flow-certificate.json').read_text())['runs'][0];r=json.loads((P/'fixed-anchor-convex-probe.json').read_text())['runs'][0];D=a['incidence_matrix'];z=[[F(x)for x in v]for v in a['flow_vectors']];C=np.array(r['centers']);A=np.array(r['anchors']);faces=r['faces'];owners=r['owners'];nf=len(faces);nv=len(D[0]);keys=[('f',i,v)for i,f in enumerate(faces)for v in f]+[('a',i,v)for i,vs in enumerate(owners)for v in vs];lookup={key:i for i,key in enumerate(keys)};zz=[[F(0),F(0)]for _ in z];maps=[]
for sx,sy in [(1,1),(1,-1),(-1,1),(-1,-1)]:
 s=np.array([sx,sy]);vm=[int(np.argmin(np.linalg.norm(C-c*s,axis=1)))for c in C];am=[int(np.argmin(np.linalg.norm(A-v*s,axis=1)))for v in A];assert np.max(np.abs(C[vm]-C*s))<1e-12 and np.max(np.abs(A[am]-A*s))<1e-12;fm=[next(j for j,g in enumerate(faces)if set(g)=={vm[v]for v in f})for f in faces];em=[lookup[(kind,(fm if kind=='f'else am)[i],vm[v])]for kind,i,v in keys];assert sorted(em)==list(range(len(z)))
 for e,ee in enumerate(em):
  for k,sgn in enumerate([sx,sy]):zz[ee][k]+=sgn*z[e][k]/4
 maps.append({'reflection':[sx,sy],'site_map':vm,'face_map':fm,'anchor_map':am,'incidence_map':em})
# Tune oppositepairflow to make anchorforces radial atXswitches; proposalonly.
bg=-np.array([[float(x)for x in v]for v in zz[3*nf:]]).reshape(10,2,2).sum(axis=1);h=F(format(-(A[0,0]*bg[0,1]-A[0,1]*bg[0,0])/A[0,0],'.14f'));assert h>0
for v in [8,9]:
 ae=[(i,e)for e,(kind,i,w)in enumerate(keys)if kind=='a'and w==v];assert len(ae)==2
 for i,e in ae:zz[e][1]+=h*(-1 if A[i,1]>0 else 1)
assert all(sum(F(D[e][j])*zz[e][k]for e in range(len(z)))==0 for j in range(nv)for k in range(2))
weights=[math.hypot(*map(float,v))for v in zz];N=sum(weights);W=np.array(r['witnesses']);pts=np.vstack([C,W]);resid=0;adj=[[]for _ in range(nv+1)]
for e,dr in enumerate(D):
 if not weights[e]:continue
 u=dr.index(1);v=dr.index(-1)if -1 in dr else nv;pp=pts[u]-(pts[v]if v<nv else A[keys[e][1]]);uu=np.array(list(map(float,zz[e])))/weights[e];resid+=weights[e]*np.linalg.norm(pp-r['radius']*uu)**2;adj[u].append((v,1/weights[e]));adj[v].append((u,1/weights[e]))
dist=[math.inf]*(nv+1);dist[nv]=0;pending=[(0,nv)]
while pending:
 dd,u=heapq.heappop(pending)
 if dd!=dist[u]:continue
 for v,c in adj[u]:
  if dd+c<dist[v]:dist[v]=dd+c;heapq.heappush(pending,(dist[v],v))
R=max(dist[:14]);out={'status':'exactrationalbalance_numeric_referencealignment','flow_vectors':[[str(x)for x in v]for v in zz],'symmetry_maps':maps,'positive_edges':sum(w>0 for w in weights),'all_sites_grounded':all(math.isfinite(d)for d in dist[:14]),'site_path_resistances':dist[:14],'N':N,'NRmax':N*R,'reference_weighted_alignment_residual':resid,'normalized_slack_budget_half_epsilon':(2e-5)**2/(2*r['radius']*N*R)};(P/'dual-slack-symmetric-flow.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in ['flow_vectors','symmetry_maps','site_path_resistances']})
