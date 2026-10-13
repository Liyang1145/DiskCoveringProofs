"""New joint 7factor LP, bounded 6 exchanges. Proposals not certificates."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,json,math
from scipy.optimize import linprog,differential_evolution,minimize,NonlinearConstraint
P=Path(__file__).parent
s=(P/'probe_seven_factor_actualr.py').read_text();mark='\nbounds=';assert s.count(mark)==1
ns={'__file__':str(P/'probe_seven_factor_actualr.py')};exec(s.split(mark)[0],ns)
patch=ns['patch'];margins=ns['margins'];atom=ns['ns']['ns']['atom'];base=ns['ns']['ns'];const=base['const'];nz=base['nz'];factors=base['factors'];oldoracle=base['oracle']
from probe_scale_fiber import fiber_oracle
from probe_switch_coupling import sw_oracle
cluster=[21,22,23,12,13,1,2];keep=[i for i in range(29)if i not in cluster];K=len(keep)+1
bounds=[(75/76,1),(.0233,math.pi),(.19,1),(.0233,math.pi),(.19,1),(1e-5,1-1e-5),(0,1)]

def catom(x):
 pp=patch(x)
 if pp is None:return None
 aa,bb,_=pp;v=0;m=np.zeros(nz)
 for fi,arg in zip(cluster,aa+bb):
  vv,mm=atom(fi,arg);v+=vv;m+=mm
 return v,m

def coracle(z,seed,old):
 def fun(x):
  at=catom(x)
  return 1e3 if at is None else -(at[0]+at[1]@z)
 ss=differential_evolution(fun,bounds,constraints=NonlinearConstraint(margins,0,np.inf),seed=1200+seed,popsize=12,maxiter=140,polish=False)
 options=[]
 for x in [ss.x,*old]:
  if min(margins(x))>=-1e-8 and catom(x) is not None:options.append(np.array(x))
  rr=minimize(fun,x,method='SLSQP',bounds=bounds,constraints={'type':'ineq','fun':margins},options={'maxiter':220,'ftol':1e-10})
  if min(margins(rr.x))>=-1e-8 and catom(rr.x) is not None:options.append(rr.x)
 assert options;return max(options,key=lambda x:-fun(x))

rows=[];rhs=[];seen=set()
def add(k,v,m,key):
 key=(k,str(key))
 if key in seen:return
 seen.add(key);row=np.zeros(nz+K);row[:nz]=m;row[nz+k]=-1;rows.append(row);rhs.append(-v)

def gridsep(z):
 vals=[]
 for k,fi in enumerate(keep):
  vv,mm=factors[fi];val=vv+mm@z;idx=int(np.argmax(val));add(k,vv[idx],mm[idx],('grid',idx));vals.append(float(val[idx]))
 return vals
oldpatch=[np.array(r['x']) for r in json.loads((P/'seven_factor_actualr_probe.json').read_text())['runs'] if r['method']=='SLSQP']
for i,x in enumerate(oldpatch):v,m=catom(x);add(K-1,v,m,('seed',i))
for fname in ['middle_inward_exchange_history.json','middle_inward_exchange_refined_history.json','middle_inward_fiber_exchange_history.json']:
 for row in json.loads((P/fname).read_text()):
  for k,fi in enumerate(keep):v,m=atom(fi,row['atoms'][fi]);add(k,v,m,(fname,row['round']))
z=np.array(row['z']);gridsep(z);lpbounds=[(-3,3)]*50+[(0,3)]*23+[(-3,3)]*48+[(None,None)]*K;lpbounds[72]=(0,0)
history=[]
for rnd in range(6):
 for it in range(80):
  sol=linprog(np.r_[const,np.ones(K)],A_ub=np.array(rows),b_ub=rhs,bounds=lpbounds,method='highs');assert sol.success
  z=sol.x[:nz];gv=gridsep(z)
  if all(v<=sol.x[nz+k]+1e-7 for k,v in enumerate(gv)):break
 vals=[];atoms=[]
 for k,fi in enumerate(keep):
  if fi>=20:x,v=fiber_oracle(fi,z,rnd+120)
  elif fi>=11:x,v=sw_oracle(fi,z)
  else:x,v=oldoracle(fi,z,rnd+120)
  # retain broad grid bound because its rows remain in LP; safe largerdomain
  vv,mm=atom(fi,x);add(k,vv,mm,('off',rnd));vals.append(max(float(v),gv[k]));atoms.append(np.asarray(x).tolist())
 x=coracle(z,rnd,oldpatch[-4:]);oldpatch.append(x);v,m=catom(x);add(K-1,v,m,('off',rnd));vals.append(float(v+m@z));total=float(const@z+sum(vals))
 record={'round':rnd,'finiteLP':float(sol.fun),'numeric_total':total,'z':z.tolist(),'factor_ids':keep+['cluster'],'factor_values':vals,'atoms':atoms+[x.tolist()]};history.append(record)
 (P/'joint_patch_exchange_history.json').write_text(json.dumps(history,indent=2));print(rnd,'finite',sol.fun,'numeric',total,flush=True)
