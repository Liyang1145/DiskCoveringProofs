import sympy as s,json
from interval_joint_patch import I,iv,R,z,P
from patch_smooth_jet import Jet
from width_endpoint_jet import endpoint
from joint_boundary_jet import width
from check_width_curvature import width as second
D,X=s.symbols('D X',real=True);co=(D*D-X*X)/(D*D+X*X);si=2*D*X/(D*D+X*X)
assert s.simplify(D*co+X*si-D)==0
assert s.simplify(X*co-D*si+X)==0
rows=[]
for rr,bb in [('.379','.62'),('.3795','.8'),('.37999','1')]:
 r=I(rr);b=I(bb);x0=2*b-iv.acos(r)if hasattr(iv,'acos')else 2*b-iv.atan2(iv.sqrt(1-r*r),r);w=2*iv.atan2(r*iv.sin(x0),1-r*iv.cos(x0))
 for j in [0,1]:
  ep=endpoint(Jet(r),Jet(b),j);vv=width(Jet(r),Jet(b),Jet(w),j)[0];assert ep.v.a<=vv.v.b and vv.v.a<=ep.v.b
  ww=I('.19');f=second(r,b,ww,j)[0];wjet=Jet(ww,[I(1)]+[I(0)]*6);g=width(Jet(r),Jet(b),wjet,j)[0];assert f.d.a<=g.d[0].b and g.d[0].a<=f.d.b
  rows.append({'r':rr,'b':bb,'j':j,'endpoint_difference':str(ep.v-vv.v),'derivative_difference':str(f.d-g.d[0])})
(P/'width_endpoint_control.json').write_text(json.dumps({'symbolic_rotation':True,'controls':rows},indent=2));print('symbolic rotation,6endpointidentities,6independentADderivatives PASS')
