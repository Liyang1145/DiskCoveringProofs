"""Actual-cover numeric budget slack, isolates remaining relaxation gaps."""
from boundary_radius_control import *
from joint_innernorm_probe import fval,cAn
owner={}
for a in G['anchors']:
 v=np.array([math.cos(float(a['theta'])),math.sin(float(a['theta']))])
 for i in a['owners']:owner.setdefault(i,[]).append(v)
wedges=[]
for i,(p,q) in owner.items():
 al=angle(p-C[i],q-C[i]);th=angle(p,q);actual=np.linalg.norm(p-C[i])*np.linalg.norm(q-C[i])*math.sin(al)/2+(th-math.sin(th))/2;budget=max(fval(al,0),cAn);wedges.append({'site':i,'alpha':al,'theta':th,'actual':actual,'corner_budget':budget,'slack':budget-actual})
edgeactual=sum(U*U*math.sin(beta[e])-loss[e] for e in E);edgecap=sum(U*U*math.sin(beta[e]) for e in E);triangleloss=[]
for j,f in enumerate(faces):
 ee={tuple(sorted(e))for e in combinations(f,2)};bs=[beta[e]for e in ee];L=U*U/2*min(1-math.cos(b)for b in bs)*abs(sum(bs)-math.pi);triangleloss.append((j,ee,L))
best=(0,[])
for mask in range(1<<len(faces)):
 used=set();v=0;fs=[]
 for j,ee,L in triangleloss:
  if not(mask>>j&1):continue
  if used&ee:break
  used|=ee;v+=L;fs.append(j)
 else:
  if v>best[0]:best=v,fs
out={'status':'numeric_actual_candidate_slack_diagnostic','area_residual':float(sum(x['actual']for x in wedges)+edgeactual-math.pi),'corner_area_slack':float(sum(x['slack']for x in wedges)),'edge_radius_slack':float(edgecap-edgeactual),'sum_face_loss_half':sum(x[2]for x in triangleloss)/2,'best_pack_loss':best,'wedges':wedges,'faces':[{'face':j,'loss':L}for j,ee,L in triangleloss]};(P/'candidate-slack-decomposition.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in ['wedges','faces']})
