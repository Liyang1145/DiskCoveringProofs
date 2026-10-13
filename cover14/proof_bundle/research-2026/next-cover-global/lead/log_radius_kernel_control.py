"""Calibrate fixed-beta logradius Hessian on actual candidate; numeric, not parameterbox certificate."""
from coupled_primal_probe import *
if __name__=='__main__':
 be=x0[:ne];logr=np.log(x0[ne:ne+nf]);loga=np.log(x0[ne+nf:]);H=np.zeros((nf,nf))
 for k,e in enumerate(edges):
  ff=E[e];f=ff[0];g=ff[1]if len(ff)==2 else None;b=logr[g]if g is not None else loga[bedges.index(e)];w=math.sin(be[k])/(2*(math.cosh(logr[f]-b)-math.cos(be[k])));H[f,f]+=w
  if g is not None:H[g,g]+=w;H[f,g]-=w;H[g,f]-=w
 def grad(z):
  ans=[]
  for f in range(nf):
   h=0
   for k in fedge[f]:
    e=edges[k];others=[g for g in E[e]if g!=f];lt=z[others[0]]if others else loga[bedges.index(e)];t=math.exp(lt-z[f]);h+=math.atan2(t*math.sin(be[k]),1-t*math.cos(be[k]))
   ans.append(math.pi-h)
  return np.array(ans)
 eps=1e-6;J=np.column_stack([(grad(logr+eps*np.eye(nf)[i])-grad(logr-eps*np.eye(nf)[i]))/(2*eps)for i in range(nf)]);ev=np.linalg.eigvalsh(H);out={'status':'numeric_fixed_candidate_kernel_calibration','gradient_residual':float(max(abs(grad(logr)))),'finite_difference_error':float(np.max(abs(H-J))),'eigenvalue_min':float(ev[0]),'eigenvalue_max':float(ev[-1]),'condition_number':float(ev[-1]/ev[0]),'dimension':nf};assert out['finite_difference_error']<1e-8 and ev[0]>0;(P/'log-radius-kernel-control.json').write_text(json.dumps(out,indent=2));print(out)
