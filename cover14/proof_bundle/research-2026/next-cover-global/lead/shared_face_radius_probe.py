"""Bounded candidateface sharedradius optimization; numeric only, no global bound."""
from boundary_radius_control import *
from scipy.optimize import minimize

def solve(bs,starts=12):
 def value(g):
  gs=np.r_[g,math.pi-sum(g)];ks=np.sin(gs)/np.sin(gs+bs);scale=min(1,1/max(ks));return U*U*scale*scale*sum(ks*np.sin(bs))
 def cons(g):
  gs=np.r_[g,math.pi-sum(g)];return np.r_[gs,math.pi-bs-gs]
 rng=np.random.default_rng(401);out=[]
 for k in range(starts):
  g=rng.dirichlet(np.ones(3))*math.pi
  opt=minimize(lambda g:-value(g),g[:2],constraints={'type':'ineq','fun':cons},method='SLSQP',options={'maxiter':1000,'ftol':1e-13})
  if opt.success and min(cons(opt.x))>-1e-8:out.append({'area':float(value(opt.x)),'gamma':list(opt.x)+[math.pi-sum(opt.x)]})
 return sorted(out,key=lambda x:-x['area'])
rows=[]
for j in [0,2,14,15]:
 ee=[tuple(sorted(e))for e in combinations(faces[j],2)];bs=np.array([beta[e]for e in ee]);actual=sum(U*U*math.sin(beta[e])-loss[e]for e in ee);sol=solve(bs);rows.append({'face':j,'betas':list(bs),'actual_area':float(actual),'solutions':sol});print(j,'actual',actual,'best',sol[0]if sol else None,flush=True)
(P/'shared-face-radius-probe.json').write_text(json.dumps({'status':'numeric_only12starts_perface','runs':rows},indent=2))
