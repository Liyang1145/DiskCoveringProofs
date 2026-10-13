"""Numeric positiveflow pathresistance diagnostics; not a certifiedbridge."""
import json,math,heapq
from pathlib import Path
from fractions import Fraction
P=Path(__file__).resolve().parent;a=json.loads((P/'fixed-anchor-flow-certificate.json').read_text())['runs'][0];D=a['incidence_matrix'];z=[[float(Fraction(x))for x in v]for v in a['flow_vectors']];nv=len(D[0]);root=nv;adj=[[]for _ in range(nv+1)];weights=[]
for e,dr in enumerate(D):
 w=math.hypot(*z[e]);weights.append(w)
 if w==0:continue
 u=dr.index(1);v=dr.index(-1)if -1 in dr else root;adj[u].append((v,1/w));adj[v].append((u,1/w))
dist=[math.inf]*(nv+1);dist[root]=0;pending=[(0,root)]
while pending:
 dd,u=heapq.heappop(pending)
 if dd!=dist[u]:continue
 for v,c in adj[u]:
  if dd+c<dist[v]:dist[v]=dd+c;heapq.heappush(pending,(dist[v],v))
N=sum(weights);R=max(dist[:14]);U=.33173203427623414;eps=4e-5;out={'status':'numeric_only_stability_budget','all_sites_positive_support_grounded':all(math.isfinite(x)for x in dist[:14]),'max_site_path_resistance':R,'N':N,'scale_invariant_NR':N*R,'normalized_slack_budget_for_half_local_epsilon':(eps/2)**2/(2*U*N*R),'zero_anchor_radius_error_assumed':True,'scope':'coarsepathestimate only; alignment residual notcomputed; notcertifiedbridge'};(P/'dual-slack-localization-probe.json').write_text(json.dumps(out,indent=2));print(out)
