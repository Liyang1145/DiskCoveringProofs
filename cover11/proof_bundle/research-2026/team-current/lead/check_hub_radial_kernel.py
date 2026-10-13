"""Independent analytic Hessian norm and Cartesian-vs-axis controls."""
import sympy as s,numpy as np,json
from pathlib import Path
from interval_joint_patch import I
import hub_axis_stationary as axis
import probe_lowbearing_stationary as cart
x,y=s.symbols('x y',real=True);q=x*x+y*y
H=s.Matrix([[2*x*y,y*y-x*x],[y*y-x*x,-2*x*y]])/q**2
assert s.simplify(H*H-s.eye(2)/q**2)==s.zeros(2)
assert s.simplify((s.Matrix([[x,y]])*H*s.Matrix([x,y]))[0])==0
controls=[]
for r,b1,b2,X in [(.3795,.85,.93,np.array([.48,.13])),(.376,.67,1.02,np.array([.4,-.07])),(.38,1.1,1.16,np.array([.44,.04]))]:
 Q,A=cart.setup(r,b1,b2);d=np.linalg.norm(Q[0]-Q[1]);e=(Q[0]-Q[1])/d;n=np.array([e[1],-e[0]]);T=np.array([n,e]);xy=T@(X-Q.mean(axis=0));g,h=cart.gh(X,r,b1,b2);j=axis.direct(list(map(I,[d,*xy])));ga=np.array([float(f.v.mid)for f in j]);ha=np.array([[float(f.d[k].mid)for k in [1,2]]for f in j]);ge=float(np.max(abs(ga-T@g)));he=float(np.max(abs(ha-T@h@T.T)));ae=float(np.max(abs(A-d*n/2)));assert max(ge,he,ae)<1e-12
 controls.append({'r':r,'b1':b1,'b2':b2,'X':X.tolist(),'gradient_error':ge,'hessian_error':he,'A_error':ae})
out={'angle_hessian_square_identity':'Htheta²=I/L⁴, hence norm=1/L²','radial_angle_quadratic_zero':True,'controls':controls,'scope':'exact Hessian identities plus numeric coordinate interface controls; no sampling proof'}
Path(__file__).with_name('hub_radial_kernel_control.json').write_text(json.dumps(out,indent=2));print(out)
