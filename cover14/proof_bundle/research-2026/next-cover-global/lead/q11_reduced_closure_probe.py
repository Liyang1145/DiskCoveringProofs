"""Bounded numerical mechanism test on q11 graph58; no exclusions from solver failures.
Eliminate15 realface radii via Dirichlet solution; odd turns eliminate circle arcs/scale.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np,json,math,time
from pathlib import Path
from itertools import combinations
from scipy.optimize import linprog,least_squares
from dirichlet_radius_solver import solve
P=Path(__file__).resolve().parent;U=.33173203427623414
faces=json.loads((P/'q11-pocket-catalogue.json').read_text())['entries'][58]['faces'];q=11;nf=len(faces)
edges=sorted({tuple(sorted(e))for f in faces for e in combinations(f,2)});ef=[[f for f,vs in enumerate(faces)if set(e)<=set(vs)]for e in edges];ne=len(edges);be=[k for k,fs in enumerate(ef)if len(fs)==1];ai={k:i for i,k in enumerate(be)}
assert {edges[k]for k in be}=={tuple(sorted((i,(i+1)%q)))for i in range(q)}
# cyclic anchori lies on siteedge(i,i+1); owneri lies between anchorsi-1,i.
cy=[edges.index(tuple(sorted((i,(i+1)%q))))for i in range(q)];inc=[[k for k,e in enumerate(edges)if i in e]for i in range(14)]
# Coherent-angle LP: variables beta, one gamma per face-edge, margin.
fe=[(f,k)for k,fs in enumerate(ef)for f in fs];fi={z:i for i,z in enumerate(fe)};N=ne+len(fe)+1;eq=[];rhs=[];ineq=[];br=[]
for f in range(nf):
 row=np.zeros(N)
 for ff,k in fe:
  if ff==f:row[ne+fi[f,k]]=1
 eq.append(row);rhs.append(math.pi)
for k,fs in enumerate(ef):
 row=np.zeros(N);row[k]=1
 for f in fs:row[ne+fi[f,k]]=1
 if len(fs)==2:eq.append(row);rhs.append(math.pi)
 else:row[-1]=1;ineq.append(row);br.append(math.pi)
for i in range(11,14):
 row=np.zeros(N);row[inc[i]]=1;eq.append(row);rhs.append(2*math.pi)
for i in range(q):
 row=np.zeros(N);row[inc[i]]=1;row[-1]=1;ineq.append(row);br.append(2*math.pi)
 row=np.zeros(N);row[inc[i]]=-1;row[-1]=1;ineq.append(row);br.append(-math.pi)
for j in range(ne+len(fe)):
 row=np.zeros(N);row[j]=-1;row[-1]=1;ineq.append(row);br.append(0)
obj=np.zeros(N);obj[-1]=-1
lp=linprog(obj,A_ub=ineq,b_ub=br,A_eq=eq,b_eq=rhs,bounds=[(0,math.pi)]*(N-1)+[(0,None)],method='highs');assert lp.success and lp.x[-1]>1e-5

def metric(z):
 beta=z[:ne];la=np.r_[z[ne:],-sum(z[ne:])];lr,JJ,rr=solve(beta,la,ef,ai)
 a=np.exp(la);R=np.exp(lr);alpha=np.array([2*math.pi-sum(beta[inc[i]])for i in range(q)]);delta={};ell=[]
 for i in range(q):
  k0=ai[cy[(i-1)%q]];k1=ai[cy[i]];u,v=a[k0],a[k1];al=alpha[i]
  ell.append(math.sqrt(max(1e-30,u*u+v*v-2*u*v*math.cos(al))))
  delta[i,cy[(i-1)%q]]=math.atan2(v*math.sin(al),u-v*math.cos(al));delta[i,cy[i]]=math.atan2(u*math.sin(al),v-u*math.cos(al))
 tau=[];ga=[]
 for i,k in enumerate(cy):
  g=math.atan2(R[ef[k][0]]*math.sin(beta[k]),a[ai[k]]-R[ef[k][0]]*math.cos(beta[k]));ga.append(g)
  tau.append(math.pi-2*g-delta[i,k]-delta[(i+1)%q,k])
 tau=np.array(tau)
 # edgei is owneri+1; thetaedge_i+thetaedge_i-1=2tau_i.
 theta=np.array([sum((-1)**j*tau[(i-j)%q]for j in range(q))for i in range(q)])
 L=np.roll(np.array(ell),-1);c=2*np.sin(theta/2);valid=np.r_[alpha,math.pi-alpha,tau,theta,math.pi-theta,np.array(ga),math.pi/2-np.array(ga)]
 scales=np.maximum(1e-30,c)/L;scale=float(np.exp(np.mean(np.log(scales))));rad=scale*max(max(a),max(R))
 return {'alpha':alpha,'tau':tau,'theta':theta,'ga':np.array(ga),'valid':valid,'scales':scales if min(valid)>0 else None,'radius':rad if min(valid)>0 else None,'real_radii':R,'anchor_radii':a,'face_residual':rr,'chords':c,'lengths':L}

if __name__=='__main__':
 start=time.time();z=np.r_[lp.x[:ne],np.zeros(q-1)];out={'status':'numeric_only_one_graph_bounded_mechanism_test','graph_index':58,'lp_margin':float(lp.x[-1]),'variables_after_radius_and_scale_elimination':len(z),'runs':[]}
 # No optimization yet: interface calibration is the decision gate.
 try:
  d=metric(z);out['initial']={k:(v.tolist()if isinstance(v,np.ndarray)else v)for k,v in d.items()};print('initial radius',d['radius'],'minvalid',min(d['valid']),'turnsumerror',sum(d['tau'])-2*math.pi,flush=True)
 except Exception as e:out['initial_error']=repr(e);print('initial inconclusive',repr(e),flush=True)
 if os.environ.get('N14_Q11_REPAIR')=='1':
  calls=[0];failures=[0]
  def residual(z):
   calls[0]+=1
   hidden=np.array([sum(z[inc[i]])-2*math.pi for i in range(11,14)])
   try:
    dd=metric(z);vv=dd['valid'];return np.r_[hidden,10*np.minimum(vv-.02,0)]
   except (ValueError,np.linalg.LinAlgError,OverflowError):
    failures[0]+=1;return np.r_[hidden,np.full(7*q,100.)]
  ans=least_squares(residual,z,bounds=(np.r_[np.full(ne,.03),np.full(q-1,-.7)],np.r_[np.full(ne,math.pi-.03),np.full(q-1,.7)]),max_nfev=80,ftol=1e-10,xtol=1e-10,gtol=1e-10)
  rec={'stage':'positive_geometry_only_not_cyclic_cover','success':bool(ans.success),'message':ans.message,'nfev':ans.nfev,'calls':calls[0],'failed_radius_solves':failures[0],'residual_norm':float(np.linalg.norm(ans.fun)),'solution':ans.x.tolist()}
  try:
   dd=metric(ans.x);rec.update({'min_validity':float(min(dd['valid'])),'hidden_angle_residual':float(max(abs(ans.fun[:3]))),'scale_spread':None if dd['scales']is None else float(max(dd['scales'])-min(dd['scales'])),'radius_proposal_not_cover':dd['radius']})
  except Exception as e:rec['error']=repr(e)
  out['runs'].append(rec);print({k:v for k,v in rec.items()if k!='solution'},flush=True)
 out['seconds']=time.time()-start;(P/'q11-reduced-closure-probe.json').write_text(json.dumps(out,indent=2))
