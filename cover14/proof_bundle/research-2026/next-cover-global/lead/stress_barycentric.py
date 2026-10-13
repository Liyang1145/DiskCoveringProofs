"""Independent candidate stress: analytically eliminate witness equilibrium via barycentrics.
Numerical proposal only. Root strings -> mp -> matrix -> scipy; all precision loss explicit.
"""
import json,itertools
from pathlib import Path
import mpmath as mp
import numpy as np
from scipy.optimize import linprog
mp.mp.dps=80
P=Path(__file__).resolve().parent
root=json.loads((P/'root-scout.json').read_text());r=mp.mpf(root['z_c_r'][2])
# Use exact-rational literal ordering, high precision conversion before float matrix stage.
data=json.loads((P/'improved-upper-test.json').read_text())
from fractions import Fraction
C=[tuple(mp.mpf(Fraction(t).numerator)/Fraction(t).denominator for t in p)for p in data['centers']]
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def norm(a):return mp.sqrt(dot(a,a))
faces=[]
for ids in itertools.combinations(range(14),3):
 a,b,c=[C[i]for i in ids];M=mp.matrix([[2*(b[0]-a[0]),2*(b[1]-a[1])],[2*(c[0]-a[0]),2*(c[1]-a[1])]])
 if abs(mp.det(M))<mp.mpf('1e-70'):continue
 w=tuple(mp.lu_solve(M,mp.matrix([dot(b,b)-dot(a,a),dot(c,c)-dot(a,a)])))
 ds=[norm(sub(p,w))for p in C];rad=ds[ids[0]]
 if norm(w)>1 or min(ds)<rad-mp.mpf('1e-55'):continue
 if abs(rad-r)>mp.mpf('1e-45'):continue
 B=mp.matrix([[C[i][0]for i in ids],[C[i][1]for i in ids],[1]*3]);beta=list(mp.lu_solve(B,mp.matrix([*w,1])))
 assert min(beta)>0
 faces.append((ids,w,beta))
assert len(faces)==14
# Circle endpoints; group numerical coincidences. Order arbitrary cut away from endpoints.
endpoints=[]
for i,p in enumerate(C):
 rho=norm(p)
 if rho<1-r:continue
 angle=mp.atan2(p[1],p[0]);half=mp.acos((1+rho*rho-r*r)/(2*rho))
 for sg in(-1,1):endpoints.append(((angle+sg*half)%(2*mp.pi),i))
endpoints.sort();anchors=[]
for th,i in endpoints:
 if anchors and abs(th-anchors[-1][0])<mp.mpf('1e-45'):anchors[-1][1].append(i)
 else:anchors.append([th,[i]])
assert len(anchors)==10 and all(len(ids)==2 for _,ids in anchors)
gaps=[(anchors[(j+1)%10][0]-anchors[j][0])%(2*mp.pi)for j in range(10)];cap=[j for j,x in enumerate(gaps)if abs(x-2*mp.asin(r))<mp.mpf('1e-45')];assert len(cap)==2
edges=[(j,i)for j,(_,ids)in enumerate(anchors)for i in ids]
# 14 face weights (sum incident beta=1),20 anchor weights,c,2 mu; common-positive t optional.
n=37;A=mp.matrix(39,n);rhs=mp.matrix(39,1);rhs[38]=1
tau=mp.matrix(10,n)
for f,(ids,w,beta)in enumerate(faces):
 for i,b in zip(ids,beta):
  for k in range(2):A[2*i+k,f]=b*(C[i][k]-w[k])
 A[38,f]=1
for e,(j,i)in enumerate(edges):
 th=anchors[j][0];a=(mp.cos(th),mp.sin(th));t=(-a[1],a[0]);col=14+e
 for k in range(2):A[2*i+k,col]=C[i][k]-a[k]
 tau[j,col]=2*dot(sub(a,C[i]),t);A[38,col]=1
for k in range(10):
 for col in range(34):A[28+k,col]=sum(tau[j,col]for j in range(k+1,10))
 A[28+k,34]=-1
 if k in cap:A[28+k,35+cap.index(k)]=1
Af=np.array(A.tolist(),float);bf=np.array(rhs.tolist(),float).ravel()
U,S,Vh=np.linalg.svd(Af,full_matrices=False);rank=int(sum(S>1e-12));Ar=Vh[:rank];br=(U[:,:rank].T@bf)/S[:rank]
# Reducing equality rows is numeric preconditioning, not proof of rank.
bounds=[(0,None)]*34+[(None,None)]+[(0,None)]*2
c=np.zeros(n)
res=linprog(c,A_eq=Ar,b_eq=br,bounds=bounds,method='highs')
out={'status':'numeric_only','face_count':14,'anchor_count':10,'cap_indices':cap,'barycentrics_min':mp.nstr(min(b for _,_,beta in faces for b in beta),30),'singular_values':S.tolist(),'numeric_rank_threshold_1e-12':rank,'feasible':bool(res.success),'lp_message':res.message,'matrix_precision_note':'mp80 input, explicitly float64 LP after construction; no certified rank or cone decision'}
if res.success:
 x=res.x;out.update(weights=x.tolist(),full_eq_max_residual=float(max(abs(Af@x-bf))),mu=x[35:37].tolist(),minimum_weight=float(min(x[:34])))
 # Find interior relative to original 34 stress weights.
 obj=np.zeros(n+1);obj[-1]=-1
 Aub=np.zeros((34,n+1))
 for i in range(34):Aub[i,i]=-1;Aub[i,-1]=1
 R=linprog(obj,A_ub=Aub,b_ub=np.zeros(34),A_eq=np.column_stack((Ar,np.zeros(rank))),b_eq=br,bounds=bounds+[(0,None)],method='highs')
 out['strict_positive_lp_success']=bool(R.success)
 if R.success:
  out['max_uniform_weight']=float(R.x[-1]);out['uniform_weights']=R.x[:-1].tolist();out['uniform_residual']=float(max(abs(Af@R.x[:-1]-bf)))
out['faces']=[{'ids':ids,'beta':[mp.nstr(b,40)for b in beta]}for ids,w,beta in faces]
out['anchors']=[{'theta':mp.nstr(th,45),'owners':ids}for th,ids in anchors]
(P/'stress-barycentric-result.json').write_text(json.dumps(out,indent=2))
np.savez(P/'stress-barycentric-matrix.npz',A=Af,b=bf)
print(json.dumps({k:v for k,v in out.items()if k not in('faces','anchors','weights','uniform_weights','singular_values')},indent=2))
