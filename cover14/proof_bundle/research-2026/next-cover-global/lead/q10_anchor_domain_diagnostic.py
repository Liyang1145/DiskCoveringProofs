"""Numeric mechanismdiagnostic only: partition versus candidateanchorcells. No bound/certificate."""
from pathlib import Path
import json,math,numpy as np
from fractions import Fraction as F
P=Path(__file__).resolve().parent

def reference_angles():
 z,c,r=[float((F(a)+F(b))/2)for a,b in json.loads((P/'root-integer-certificate.json').read_text())['box_dyadic']];s=math.sqrt(1-r*r);a=(s+z)/2;b=r+math.sqrt(r*r-(a-z)**2);d=1-math.sqrt(r*r-c*c);v1=(1+a*a+b*b-r*r)/2;v2=(1+c*c+d*d-r*r)/2;det=a*d-b*c;px=(v1*d-v2*b)/det;py=(a*v2-c*v1)/det;A=np.array([(s,r),(px,py),(0,1),(-px,py),(-s,r),(-s,-r),(-px,-py),(0,-1),(px,-py),(s,-r)]);owners=json.loads((P/'fixed-anchor-flow-certificate.json').read_text())['runs'][0]['owners'];maps=next(r for r in json.loads((P/'candidate-catalogue-match.json').read_text())['runs']if r['index']==879)['exact_matches'];out=[]
 for mm in maps:
  mm={int(k):v for k,v in mm.items()};mapped=[set(mm[v]for v in pp)for pp in owners];order=[mapped.index({j,(j+1)%10})for j in range(10)];theta=np.angle(A[:,0]+1j*A[:,1])[order];tt=(theta-theta[0])%(2*math.pi)
  if np.any(np.diff(tt)<0):tt=(-theta+theta[0])%(2*math.pi)
  assert np.all(np.diff(tt)>0);out.append({'map':mm,'anchor_order':order,'angles':tt.tolist()})
 return out
if __name__=='__main__':
 ref=reference_angles();a=json.loads((P/'q10-polytope-partition-879.json').read_text());L=2*math.asin(.33173203427623414);records=[]
 for n in a['nodes']:
  if n.get('status')!='split':continue
  V=np.array([[float(F(t[0]))*L+float(F(t[1]))*2*math.asin(2*.33173203427623414)+float(F(t[2]))*2*math.pi for t in v]for v in n['polytope']['vertex_set']]);TT=np.arange(10)*L-np.c_[np.zeros(len(V)),np.cumsum(V[:,:-1],axis=1)];mid=TT.mean(axis=0);worst=min(np.max(np.abs(TT-np.array(r['angles'])))for r in ref);dist=min(np.max(np.abs(mid-np.array(r['angles'])))for r in ref);records.append({'node':n['id'],'max_angle_width':float(np.ptp(TT,axis=0).max()),'center_candidate_distance':float(dist),'wholecell_candidate_distance':float(worst),'radius':n['flow_proposal']['radius'],'robust':n['flow_proposal']['robust_value']})
 out={'status':'numeric_only_mapping_and_cell_diagnostic','references':ref,'nodes':records};(P/'q10-anchor-domain-diagnostic.json').write_text(json.dumps(out,indent=2));print('references',len(ref));print('last',records[-8:]);print('closest',sorted(records,key=lambda r:r['center_candidate_distance'])[:3])
