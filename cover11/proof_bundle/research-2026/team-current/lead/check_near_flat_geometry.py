"""Analytic identities plus asymmetric admissible point calibration. Not a collar proof."""
import sympy as S, numpy as np,math,json
from pathlib import Path
r,h,k,s,a,y=S.symbols('r h k s a y',real=True)
assert S.expand(((k-a)**2+y*y-s*s)-(r*r-h*h+y*y+a*a-2*k*a)-(k*k+h*h-s*s-r*r))==0
assert S.det(S.Matrix([[a,h-y],[a,-h-y]]))==-2*a*h
rng=np.random.default_rng(271);count=0;asymmetric=0;max_ratio=0
for _ in range(20000):
 rr=rng.uniform(.375,.38);ss=math.sqrt(1-rr*rr);w=rng.uniform(.5,2*math.asin(rr));hh=math.sin(w/2);kk=math.cos(w/2);aa=rng.uniform(0,.15);yy=rng.uniform(-.04,.04)
 if (kk-aa)**2+yy*yy>ss*ss or aa*aa+(hh+abs(yy))**2>rr*rr:continue
 u=np.array([aa,hh-yy]);v=np.array([aa,-hh-yy]);alpha=math.atan2(abs(np.linalg.det(np.array([u,v]))),u@v);eps=math.pi-alpha
 if eps>math.pi/2:continue
 A=rr*rr*math.sin(eps)/(2*math.sin(.5/2));vals=[aa/A,abs(yy)/(2*A/rr),math.hypot(kk-aa-ss,yy)/(A*math.sqrt((1+1/ss)**2+(2/rr)**2)),(2*math.asin(rr)-w)/(4*A/(rr*ss))]
 assert max(vals)<=1+1e-12;count+=1;asymmetric+=abs(yy)>1e-8;max_ratio=max(max_ratio,max(vals))
out={'symbolic_norm_expansion':True,'symbolic_cross_product':True,'asymmetric_legal_point_controls':count,'asymmetric':asymmetric,'largest_bound_ratio':max_ratio,'scope':'analytic proof in NEAR-FLAT-SECTOR-GEOMETRY.md; point controls not completeness'}
Path(__file__).with_name('near_flat_geometry_control.json').write_text(json.dumps(out,indent=2));print(out)
