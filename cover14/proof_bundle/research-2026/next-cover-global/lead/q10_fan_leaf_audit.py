"""Independent completeactivebasis enumeration ofnode1+twofan cuts andFractionflowreplay."""
from q11_split_inductive_audit import inv,sign,subtract,ZERO,Q,P,json
from q11_chord_flow_fraction_replay import replay
from itertools import combinations
import hashlib

def val(n,v):return tuple(sum(n[j]*v[j][h]for j in range(10))for h in range(3))
if __name__=='__main__':
 src=P/'q10-fan-pending-control.json';data=json.loads(src.read_text());run=next(r for r in data['runs']if r['node']==1);poly=run['polytope'];eq=([Q(1)]*10,(Q(10),Q(0),Q(-1)));assert list(map(Q,poly['equality'][0]))==eq[0]and tuple(map(Q,poly['equality'][1]))==eq[1];cs=[(list(map(Q,n)),tuple(map(Q,r)),lab)for n,r,lab in poly['inequalities']];assert len(cs)==13
 for j,(n,r,_)in enumerate(cs[:10]):assert n==[Q(i==j)for i in range(10)]and r==ZERO
 original=json.loads((P/'q10-polytope-partition-879-audit-snapshot.json').read_text());rep=original['nodes'][0]['split_report'];assert original['nodes'][0]['children'][0]==1;assert cs[10][:2]==(list(map(Q,rep['normal'])),tuple(map(Q,rep['rhs'])))
 for (n,r,lab),ids in zip(cs[11:],[[8,9,0,1],[3,4,5,6]]):assert n==[Q(i in ids)for i in range(10)]and r==tuple(Q(5,24)*x for x in eq[1])
 VV=set();nonsingular=0
 for comb in combinations(range(len(cs)),9):
  M=[eq[0]]+[cs[i][0]for i in comb];MI=inv(M)
  if MI is None:continue
  nonsingular+=1;bb=[eq[1]]+[cs[i][1]for i in comb];v=tuple(tuple(sum(MI[i][k]*bb[k][h]for k in range(10))for h in range(3))for i in range(10))
  if all(sign(subtract(val(n,v),r))>=0 for n,r,lab in cs):VV.add(v)
 canon=lambda vs:{tuple(tuple(map(Q,t))for t in v)for v in vs};assert VV==canon(poly['vertex_set'])==canon(run['certificate']['polytope']['vertices']);faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][879]['faces'];assert run['certificate']['flow']['faces']==faces and run['certificate']['index']==879;rr=replay(run['certificate']);assert rr['excluded'];out={'status':'sourcebound_node1_excluded_under_C1331_fancuts','vertices':len(VV),'nonsingular_bases':nonsingular,'replay':rr,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'snapshot_sha256':hashlib.sha256((P/'q10-polytope-partition-879-audit-snapshot.json').read_bytes()).hexdigest(),'scope':'node1 entirefeasible879 domain using necessaryC1331 cuts; notwholeq10'};(P/'q10-fan-leaf-audit.json').write_text(json.dumps(out,indent=2));print('FANLEAF',len(VV),rr['lower_radius_exact'])
