"""Numeric rank diagnostic only, compares independent geometry to radius/angle constraints."""
from boundary_cyclicity_control import *
from scipy.linalg import qr
from scipy.optimize._numdiff import approx_derivative
if __name__=='__main__':
 out=[];data=json.loads((P/'coupled-primal-probe.json').read_text())['runs']
 for j,z in[(-1,x0)]+[(r['start'],np.array(r['solution']))for r in data]:
  fn=lambda z:np.r_[unpack(z)[1],cyclicity(z)];jac=approx_derivative(fn,z,method='3-point');sv=np.linalg.svd(jac,compute_uv=False);base=np.linalg.svd(jac[:nf+len(hidden)+1],compute_uv=False);qq,rr,piv=qr(jac.T,pivoting=True,mode='economic');rec={'start':j,'singular_values':sv.tolist(),'base_singular_values':base.tolist(),'rank_1e-7':int(sum(sv>1e-7)),'variables':len(z),'row_pivots':piv.tolist()};out.append(rec);print(j,'rank',rec['rank_1e-7'],'smallest',sv[-5:],flush=True)
 (P/'cyclicity-rank-control.json').write_text(json.dumps({'status':'numeric_rank_diagnostic_only','runs':out},indent=2))
