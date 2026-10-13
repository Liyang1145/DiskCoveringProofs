"""Diagnostic only: all shared metric and circle closure constraints; minimize radius.
Candidate calibration, rank audit, bounded local solves, no global assertion.
"""
import numpy as np,json,math
from pathlib import Path
from scipy.spatial import Delaunay
from scipy.optimize import minimize
from scipy.linalg import qr
P=Path(__file__).parent;pi=math.pi
raw=json.loads(Path('n11/upper/certified_object.json').read_text(encoding='utf-8-sig'));C=np.array([[int(v)/1e17 for v in a] for a in raw['centers_scaled_1e17']]);rings=sorted([i for i in range(11) if i not in [0,2]],key=lambda i:math.atan2(C[i,1],C[i,0]));C=C[rings+[0,2]]
faces=json.loads((P/'q0_graphs.json').read_text())[2]['faces'];target={tuple(sorted(f)) for f in faces}
for shift in range(9):
 for swap in range(2):
  c=C[[(i+shift)%9 for i in range(9)]+([10,9] if swap else [9,10])]
  if {tuple(sorted(f)) for f in Delaunay(c).simplices}==target:break
 else:continue
 break
else:raise AssertionError('graph mapping failed')
edges=sorted({tuple(sorted((f[k],f[(k+1)%3]))) for f in faces for k in range(3)})
ang=[];rho=[];switch=[];bb=[]
for f in faces:
 p=c[f];v=np.linalg.solve(2*(p[1:]-p[0]),(p[1:]**2).sum(1)-(p[0]**2).sum());rho.append(np.linalg.norm(v-p[0]))
 for k in range(3):
  u=p[(k+1)%3]-p[k];w=p[(k+2)%3]-p[k];ang.append(math.acos(np.clip(u@w/np.linalg.norm(u)/np.linalg.norm(w),-1,1)))
for i in range(9):
 j=(i+1)%9;d=np.linalg.norm(c[j]-c[i]);m=(c[j]+c[i])/2;n=np.array([(c[j]-c[i])[1],-(c[j]-c[i])[0]])/d;l=-m@n+math.sqrt((m@n)**2+1-m@m);p=m+l*n;switch.append(p);rho.append(np.linalg.norm(p-c[i]));bb.append(math.atan2(d/2,l))
R=max(rho);x0=np.r_[ang,bb,np.log(np.array(rho)/R),math.log(R)]
A=np.zeros((21,63));B=A.copy();U=A.copy();V=A.copy();eq=np.zeros((13,63));rhs=np.r_[np.ones(11)*pi,[2*pi,2*pi]];alpha=np.zeros((9,63));ac=np.ones(9)*pi
for t,f in enumerate(faces):
 eq[t,3*t:3*t+3]=1
 for k,i in enumerate(f):
  if i<9:alpha[i,3*t+k]=-1
  else:eq[11+i-9,3*t+k]=1
for ei,(i,j) in enumerate(edges):
 adj=[(t,f.index(next(v for v in f if v not in (i,j)))) for t,f in enumerate(faces) if i in f and j in f];t,k=adj[0];A[ei,3*t+k]=1;U[ei,42+t]=1
 if len(adj)==2:t,k=adj[1];B[ei,3*t+k]=1;V[ei,42+t]=1
 else:
  bi=next(b for b in range(9) if {b,(b+1)%9}=={i,j});B[ei,33+bi]=1;V[ei,53+bi]=1;alpha[i,33+bi]+=1;alpha[j,33+bi]+=1

def calc(x):
 a=ac+alpha@x;y=np.exp(x[53:62]+x[62]);u=np.roll(y,1);v=y;q=(u-v)**2+4*u*v*np.sin(a/2)**2;w=2*np.arcsin(np.sqrt(np.clip(q,1e-18,3.999))/2)
 L=np.arctan2(v*np.sin(a),u-v*np.cos(a));T=pi-a-L
 closure=T+np.roll(L,-1)+2*x[33:42]+(w+np.roll(w,-1))/2-pi
 area=np.sum(np.exp((U+V)@x+2*x[62])*np.sin((A+B)@x))+np.sum(u*v*np.sin(a)/2+(w-np.sin(w))/2)
 return a,w,closure,area

def ceq(x):return np.r_[eq@x-rhs,(U-V)@x+np.log(np.sin(A@x))-np.log(np.sin(B@x)),calc(x)[2]]
def cineq(x):
 a,w,cl,area=calc(x);return np.r_[a,pi-a,pi-(A+B)@x]
res=ceq(x0);assert max(abs(res))<1e-10
h=1e-6;jac=np.column_stack([(ceq(x0+np.eye(63)[k]*h)-ceq(x0-np.eye(63)[k]*h))/(2*h) for k in range(63)])
sv=np.linalg.svd(jac,compute_uv=False);rank=int(sum(sv>1e-7));_,_,piv=qr(jac.T,pivoting=True);keep=piv[:rank]
print('calibration',max(abs(res)),'area',calc(x0)[3],'R',R,'eq rank',rank,'eqs',len(res),flush=True)
out={'candidate_radius':R,'candidate_residual':max(abs(res)),'rank_numeric':rank,'singular_values':sv.tolist(),'x0':x0.tolist(),'faces':faces,'edges':edges,'runs':[]}
bounds=[(1e-6,pi-1e-6)]*33+[(1e-6,pi/2-1e-6)]*9+[(-5,0)]*20+[(math.log(.35),math.log(.4))]
rng=np.random.default_rng(820)
for trial in range(3):
 seed=x0.copy()
 if trial:seed[:42]+=rng.normal(0,.006,42);seed[42:62]=np.minimum(0,seed[42:62]+rng.normal(0,.002,20))
 o=minimize(lambda x:x[-1],seed,method='SLSQP',bounds=bounds,constraints=[{'type':'eq','fun':lambda x:ceq(x)[keep]},{'type':'ineq','fun':cineq}],options={'maxiter':350,'ftol':1e-12})
 row={'trial':trial,'success':bool(o.success),'radius':math.exp(o.x[-1]),'all_eq_residual':float(max(abs(ceq(o.x)))),'min_ineq':float(min(cineq(o.x))),'area':float(calc(o.x)[3]),'active_radii':int(sum(o.x[42:62]>-1e-7)),'x':o.x.tolist()};out['runs'].append(row);print({k:v for k,v in row.items() if k!='x'},flush=True)
 (P/'q0_exact_closure_radius.json').write_text(json.dumps(out,indent=2))
