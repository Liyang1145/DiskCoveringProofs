"""Symbolic derivative and numeric saved-object calibration, not cover certification."""
import sympy as sp
from boundary_cyclicity_control import *
if __name__=='__main__':
 ss,cc=sp.symbols('s c',real=True);aa=1+ss**2-2*ss*cc;assert sp.expand(ss**2*(1-cc**2)-aa*ss*cc-ss*(ss-cc)*(1-ss*cc))==0
 s=math.sqrt(1-U*U);out=[];data=json.loads((P/'coupled-primal-probe.json').read_text())['runs'];q=nb
 for j,z in[(-1,x0)]+[(row['start'],np.array(row['solution']))for row in data]:
  radii=U*z[ne+nf:];angular=[math.acos(min(1,max(-1,(1+s*s-a*a)/(2*s))))for a in radii];out.append({'start':j,'perimeter_slack':sum(angular)-math.pi,'anchor_deficit_sum':float(sum(U-radii)),'linear_deficit_cap':s*(q*math.asin(U)-math.pi),'mean_radius_lower':math.sqrt(1+s*s-2*s*math.cos(math.pi/q)),'mean_radius':float(np.mean(radii))})
 (P/'shared-anchor-perimeter-control.json').write_text(json.dumps({'status':'symbolic_derivative_identity_and_numeric_calibration','runs':out},indent=2));print('derivativefactor verified; candidate perimeter slack',out[0]['perimeter_slack'],'linearcap',out[0]['linear_deficit_cap'],'meanlower',out[0]['mean_radius_lower']);print('savednearcovers minslack',min(x['perimeter_slack']for x in out))
