"""Exact incidence plus numerical shape calibration for angle-only elimination."""
from pathlib import Path
import numpy as np,json,math,collections
P=Path(__file__).parent
ns={'__file__':str(P/'q0_exact_closure_radius.py')};exec((P/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0],ns)
A,B,U,V,eq,rhs,alpha,ac=[ns[k] for k in ['A','B','U','V','eq','rhs','alpha','ac']]
edge=[];adj=collections.defaultdict(list)
for k in range(21):
 f=int(np.argmax(U[k,42:62]));g=int(np.argmax(V[k,42:62]));edge.append((f,g));adj[f].append((g,k,1));adj[g].append((f,k,-1))
assert len(edge)==21 and len(adj)==20
Alt=np.array([[(-1)**((j-i)%9) for j in range(9)] for i in range(9)])
def radii(a,root=0):
 ls=np.log(np.sin(A[:,:42]@a))-np.log(np.sin(B[:,:42]@a));logg=np.zeros(20);seen={root};todo=[root];tree=[]
 for f in todo:
  for g,k,d in adj[f]:
   if g not in seen:seen.add(g);todo.append(g);tree.append(k);logg[g]=logg[f]+d*ls[k]
 assert len(seen)==20 and len(tree)==19
 other=sorted(set(range(21))-set(tree));assert len(other)==2
 cy=np.array([logg[f]-logg[g]+ls[k] for k,(f,g) in enumerate(edge)])[other]
 return logg,cy,tree,other

def shape(a,root=0):
 logg,cy,tree,other=radii(a,root);g=np.exp(logg);al=ac+alpha[:,:42]@a;u=np.roll(g[11:],1);v=g[11:];ell=np.sqrt((u-v)**2+4*u*v*np.sin(al/2)**2);L=np.arctan2(v*np.sin(al),u-v*np.cos(al));T=math.pi-al-L;tau=math.pi-T-np.roll(L,-1)-2*a[33:42];w=Alt@tau;rat=2*np.sin(w/2)/ell
 return max(g)*rat[0],np.r_[eq[:,:42]@a-rhs,cy,rat[1:7]/rat[0]-1],{'logg':logg,'cycle':cy,'w':w,'rat':rat,'tree':tree,'other':other,'alpha':al}
a=ns['x0'][:42];R,con,detail=shape(a);assert max(abs(con))<1e-12
rr=[]
for root in range(20):
 r,c,d=shape(a,root);rr.append(r);assert max(abs(c))<1e-12
assert max(rr)-min(rr)<1e-14
# Compare against independently obtained face circumradii and switch endpoint radii.
logs=ns['x0'][42:62];assert max(abs(detail['logg']-(logs-logs[0])))<1e-13
h=1e-6;J=np.column_stack([(shape(a+np.eye(42)[k]*h)[1]-shape(a-np.eye(42)[k]*h)[1])/(2*h) for k in range(42)]);sv=np.linalg.svd(J,compute_uv=False);rank=int(sum(sv>1e-7));assert rank==21
out={'scope':'exact graph incidence, numerical calibration only; proof in ANGLE-ONLY-EXACT-MODEL.md','nodes':20,'edges':21,'tree_edges':detail['tree'],'non_tree_edges':detail['other'],'radius':R,'root_invariance_spread':max(rr)-min(rr),'candidate_residual':float(max(abs(con))),'logratio_error':float(max(abs(detail['logg']-(logs-logs[0])))),'angles':42,'rows':21,'numeric_rank':rank,'singular_values':sv.tolist(),'active_max_radii_numeric':int(sum(abs(detail['logg']-max(detail['logg']))<1e-7))}
(P/'angle_only_control.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
