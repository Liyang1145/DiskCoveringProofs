"""Bounded interface test: enforce cyclicity on saved false-nearcover solutions. Not optimum evidence."""
from boundary_cyclicity_control import *
from coupled_primal_reconstruct import reconstruct
from scipy.optimize import least_squares
import time
if __name__=='__main__':
 data=json.loads((P/'coupled-primal-probe.json').read_text())['runs'];out=[];start=time.time()
 for row in data[1:]:
  z=np.array(row['solution']);fun=lambda z:np.r_[unpack(z)[1],cyclicity(z)];lo=np.r_[np.full(ne,1e-5),np.full(nf+nb,.1)];hi=np.r_[np.full(ne,math.pi-1e-5),np.ones(nf+nb)];z=np.minimum(hi-1e-12,np.maximum(lo+1e-12,z));res=least_squares(fun,z,bounds=(lo,hi),gtol=2e-14,ftol=2e-14,xtol=2e-14,max_nfev=1200);geom=reconstruct(res.x);eq=fun(res.x);rec={'start':row['start'],'success':bool(res.success),'nfev':int(res.nfev),'max_residual':float(max(abs(eq))),'max_candidate_parameter_change':float(max(abs(res.x-x0))),'alpha_min':float(min(unpack(res.x)[2])),'alpha_max':float(max(unpack(res.x)[2])),'geometry':geom,'solution':res.x.tolist()};out.append(rec);print({k:v for k,v in rec.items()if k not in ['geometry','solution']},'anchor_error',geom['max_unit_anchor_error'],'seconds',time.time()-start,flush=True)
 (P/'cyclicity-repair-control.json').write_text(json.dumps({'status':'numeric_interface_test_only','runs':out},indent=2))
