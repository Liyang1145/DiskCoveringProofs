"""Direct Cartesian disk residual controls for penalty majorants, no feasibility clipping."""
import json,math
from interval_joint_patch import I,P
from penalized_low_boundary import residuals
from probe_lowbearing_stationary import residuals as cart
rows=[]
for j in range(3):
 for b1,b2,p in [(.84,.85,.1),(.7,.9,-.2),(.95,.8,.3)]:
  r=.3795
  if j<2:
   H=2*r*math.sin(2*b1-p)if j==0 else 2*r*math.sin(2*b2+p);v,t=H*math.cos(p),H*math.sin(p)
  else:p+=math.pi;v=math.sqrt(1-r*r)+(1-r)*math.cos(p);t=(1-r)*math.sin(p)
  gs=residuals(list(map(I,[r,b1,b2,p])),j);cc=cart([v,t],r,b1,b2);err=max(abs(float(a.v.mid)-b)for a,b in zip(gs,cc[:3]));assert err<1e-12
  rows.append({'branch':j,'point':[r,b1,b2,p],'residual_error':err,'own_circle_residual':float(gs[j].v.mid)})
(P/'penalty_interface_control.json').write_text(json.dumps({'controls':rows,'inequality':'For feasible g<=0 and fixed rational lambda>=0, F<=F-lambda*g. Full-extension MVT bounds penalized expression; no stationarity premise.'},indent=2));print('9 independentCartesianresidualchecks passed')
