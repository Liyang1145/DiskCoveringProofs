"""Numeric test of local boundary cyclicity equations, actual geometry vs relaxed near-cover."""
from coupled_primal_probe import *
def cyclicity(z):
 be=z[:ne];xr=z[ne:ne+nf];ya=z[ne+nf:];al=np.array([2*math.pi-sum(be[k]for k in inc[v])for v in boundary]);theta={};delta={}
 for v,a,(i,j)in zip(boundary,al,bi):
  u,w=ya[i],ya[j];ch=U*math.sqrt(max(0,u*u+w*w-2*u*w*math.cos(a)));theta[v]=2*math.asin(min(1,ch/2));delta[v,i]=math.atan2(w*math.sin(a),u-w*math.cos(a));delta[v,j]=math.atan2(u*math.sin(a),w-u*math.cos(a))
 residual=[]
 for i,e in enumerate(bedges):
  u,v=e;k=edges.index(e);f=E[e][0];g=math.atan2(xr[f]*math.sin(be[k]),ya[i]-xr[f]*math.cos(be[k]));residual.append(2*g+delta[u,i]+delta[v,i]+(theta[u]+theta[v])/2-math.pi)
 return np.array(residual)
if __name__=='__main__':
 data=json.loads((P/'coupled-primal-probe.json').read_text())['runs'];out=[]
 for j,z in [(-1,x0)]+[(r['start'],np.array(r['solution']))for r in data]:
  v=cyclicity(z);out.append({'start':j,'max_abs_cyclicity':float(max(abs(v))),'sum_residual':float(sum(v)),'residuals':v.tolist()});print(j,max(abs(v)),sum(v),flush=True)
 assert out[0]['max_abs_cyclicity']<1e-12
 (P/'boundary-cyclicity-control.json').write_text(json.dumps({'status':'numeric_local_cyclicity_control','runs':out},indent=2))
