"""Bounded numeric minimization ON closure manifold of q11/58, not graph exclusion."""
from q11_reduced_closure_probe import *
from scipy.optimize import minimize
from scipy.optimize._numdiff import approx_derivative
from scipy.linalg import qr
from functools import lru_cache
@lru_cache(maxsize=256)
def mm(t):return metric(np.array(t))
def eq(z):
 d=mm(tuple(z));L=d['lengths'];c=d['chords'];scale=float(c@L/(L@L));return np.r_[[sum(z[inc[i]])-2*math.pi for i in range(11,14)],scale*L-c]
saved=json.loads((P/'q11-closure-repair.json').read_text());z=np.array(saved['runs'][0]['solution']);J=approx_derivative(eq,z);sv=np.linalg.svd(J,compute_uv=False);_,_,piv=qr(J.T,pivoting=True,mode='economic');rank=int(sum(sv>1e-7));ids=piv[:rank];assert rank==11
start=time.time();fails=[0];best=[None]
def eq_selected(x):
 try:return eq(x[:-1])[ids]
 except (ValueError,OverflowError,np.linalg.LinAlgError):fails[0]+=1;return np.full(rank,100.)
def ine(x):
 try:
  d=mm(tuple(x[:-1]));scale=float(d['chords']@d['lengths']/(d['lengths']@d['lengths']));rad=np.r_[d['real_radii'],d['anchor_radii']]*scale
  return np.r_[d['valid']-1e-6,x[-1]-rad]
 except (ValueError,OverflowError,np.linalg.LinAlgError):fails[0]+=1;return np.full(7*q+nf+q,-100.)
x=np.r_[z,saved['runs'][0]['radius_if_closure_holds']];calls=[0]
def callback(x):
 calls[0]+=1
 if calls[0]%20==0:print('iter',calls[0],'radius',x[-1],'eq',max(abs(eq_selected(x))),'ineq',min(ine(x)),flush=True)
a=minimize(lambda x:x[-1],x,method='SLSQP',constraints=[{'type':'eq','fun':eq_selected},{'type':'ineq','fun':ine}],bounds=[(.01,math.pi-.01)]*ne+[(-1.5,1.5)]*(q-1)+[(.25,.6)],options={'maxiter':150,'ftol':1e-11},callback=callback)
out={'status':'numeric_only_not_exclusion','graph_index':58,'jacobian_singular_values':sv.tolist(),'selected_equation_rows':ids.tolist(),'initial_numeric_rank':rank,'success':bool(a.success),'message':a.message,'iterations':a.nit,'radius':float(a.x[-1]),'all_closure_residual':float(max(abs(eq(a.x[:-1])))),'minimum_inequality':float(min(ine(a.x))),'failed_radius_solves':fails[0],'solution':a.x.tolist(),'seconds':time.time()-start};(P/'q11-exact-closure-optimize.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k not in ['solution','jacobian_singular_values']},flush=True)
