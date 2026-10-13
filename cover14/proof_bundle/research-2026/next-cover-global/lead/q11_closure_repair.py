"""One bounded q11/58 joint-closure test, radius elimination, no certification."""
from q11_reduced_closure_probe import *
from functools import lru_cache
start=time.time();saved=json.loads((P/'q11-reduced-closure-probe.json').read_text());z=np.array(saved['runs'][0]['solution']);calls=[0];fail=[0]
@lru_cache(maxsize=256)
def cached(t):return metric(np.array(t))
def residual(z,cap=False):
 calls[0]+=1;hidden=np.array([sum(z[inc[i]])-2*math.pi for i in range(11,14)])
 try:
  d=cached(tuple(z));L=d['lengths'];c=d['chords'];scale=float(c@L/(L@L));closure=(scale*L-c);valid=d['valid'];r=scale*max(max(d['real_radii']),max(d['anchor_radii']))
  return np.r_[hidden,closure,3*np.minimum(valid-1e-5,0),max(0,r-U) if cap else 0]
 except (ValueError,OverflowError,np.linalg.LinAlgError):fail[0]+=1;return np.r_[hidden,np.full(q,10.),np.full(7*q,10.),10.]
lo=np.r_[np.full(ne,.01),np.full(q-1,-1.5)];hi=np.r_[np.full(ne,math.pi-.01),np.full(q-1,1.5)]
out={'status':'numeric_only_not_exclusion','graph_index':58,'runs':[],'variables':len(z)}
for cap in [False,True]:
 ans=least_squares(lambda z:residual(z,cap),z,bounds=(lo,hi),max_nfev=160,ftol=1e-11,xtol=1e-11,gtol=1e-11);z=ans.x;d=metric(z);scale=float(d['chords']@d['lengths']/(d['lengths']@d['lengths']));r=scale*max(max(d['real_radii']),max(d['anchor_radii']))
 rec={'cap_enabled':cap,'success':bool(ans.success),'nfev':ans.nfev,'residual_norm':float(np.linalg.norm(ans.fun)),'hidden_residual':float(max(abs(ans.fun[:3]))),'closure_residual':float(max(abs(ans.fun[3:3+q]))),'min_validity':float(min(d['valid'])),'radius_if_closure_holds':float(r),'solution':z.tolist(),'calls':calls[0],'failed_solves':fail[0]};out['runs'].append(rec);out['seconds']=time.time()-start;(P/'q11-closure-repair.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in rec.items()if k!='solution'},flush=True)
