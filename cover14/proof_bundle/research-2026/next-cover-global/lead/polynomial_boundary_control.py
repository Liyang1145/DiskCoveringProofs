"""Algebraic closure calibration against angle equations; numeric only."""
from boundary_cyclicity_control import *
def polynomial(z):
 be=z[:ne];xr=U*z[ne:ne+nf];ya=U*z[ne+nf:];al={v:2*math.pi-sum(be[k]for k in inc[v])for v in boundary};result=[]
 for i,(u,v)in enumerate(bedges):
  a=ya[i];k=edges.index(bedges[i]);R=xr[E[bedges[i]][0]];G=complex(a-R*math.cos(be[k]),R*math.sin(be[k]));prod=G*G;norm=abs(G)**2
  for j in[u,v]:
   oi=next(h for h in bi[boundary.index(j)]if h!=i);b=ya[oi];Z=complex(a-b*math.cos(al[j]),b*math.sin(al[j]));L=abs(Z);H=complex(math.sqrt(max(0,1-L*L/4)),L/2);prod*=Z*H;norm*=L
  result.append((prod+norm)/norm)
 return np.array(result)
if __name__=='__main__':
 data=json.loads((P/'coupled-primal-probe.json').read_text())['runs'];out=[]
 for j,z in[(-1,x0)]+[(row['start'],np.array(row['solution']))for row in data]:
  p=polynomial(z);c=cyclicity(z);agreement=max(abs(p-(1-np.exp(1j*c))));assert agreement<1e-12;out.append({'start':j,'max_polynomial_scaled':float(max(abs(p))),'max_angle_residual':float(max(abs(c))),'max_formula_agreement':float(agreement)})
 assert out[0]['max_polynomial_scaled']<1e-12
 (P/'polynomial-boundary-control.json').write_text(json.dumps({'status':'numeric_algebra_interface_control','runs':out},indent=2));print(out)
