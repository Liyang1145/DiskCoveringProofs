"""Root inclusion calibration; analytic intervalNewton proof separate."""
import json,math
from scipy.optimize import brentq
from low_stationary_contract import contract
from all_boundary_derivative import derivative
from interval_joint_patch import I,P
rows=[]
for j,lr in [(0,(-.2,.8)),(1,(-.8,.2)),(2,(2,4.2))]:
 b=[I('.3795'),I('.84'),I('.85')];xs=[lr[0]+(lr[1]-lr[0])*k/200 for k in range(201)]
 fun=lambda p:float(derivative(b+[I(p)],j).v.mid)
 for l,h in zip(xs[:-1],xs[1:]):
  if fun(l)*fun(h)>=0:continue
  root=brentq(fun,l,h,xtol=1e-14);box=b+[I(l,h)];res=contract(box,j);assert res is not None and float(res[3].a)-1e-12<=root<=float(res[3].b)+1e-12
  rows.append({'j':j,'root_numeric':root,'before':[l,h],'after':[float(res[3].a),float(res[3].b)]})
(P/'stationary_contraction_control.json').write_text(json.dumps(rows,indent=2));print(len(rows),'numericrootinclusioncontrols; NOT proof ofkernel')
