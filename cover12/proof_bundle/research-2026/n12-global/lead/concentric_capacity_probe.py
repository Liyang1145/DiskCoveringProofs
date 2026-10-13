"""Numeric-only bounded mechanism test: universal two-concentric-circle capacity.
Can radial unweighted capacities exclude k10/11? No grid success is proof.
"""
import numpy as np,json
from pathlib import Path
r=.3611029637445086726
# inner-root representatives; allow inactive hubs arbitrary and overbound their arc.
t=np.linspace(1-r,np.sqrt(1-r*r),4001)
a=np.arccos(np.clip((1+t*t-r*r)/(2*t),-1,1))
rows=[]
for k in (9,10,11):
 best=(1e9,None)
 for q in np.linspace(r+1e-4,1-r,101):
  b=np.arccos(np.clip((q*q+t*t-r*r)/(2*q*t),-1,1))
  hub=np.arcsin(r/q)
  for lam in np.linspace(0,2,401):
   residual=k*np.max(a+lam*b)+(12-k)*lam*hub-np.pi*(1+lam)
   if residual<best[0]:best=(float(residual),{'q':float(q),'lambda':float(lam),'hub_halfwidth':float(hub)})
 rows.append({'k':k,'best_sampled_residual':best[0],'parameters':best[1]})
p=Path('research-2026/n12-global/evidence/concentric-capacity-probe.json')
p.write_text(json.dumps({'level':'numeric only','radius':r,'radial_points':len(t),'q_points':101,'lambda_points':401,'decision':'negative residual would motivate rigorous continuous certification; positive residual is method diagnostic only','rows':rows},indent=2))
print(json.dumps(rows))
