"""Independent exact matrix check and coordinate numeric controls for odd boundary inversion."""
from pathlib import Path
import numpy as np,math,json,sympy as sp
P=Path(__file__).parent
n=9;A=sp.zeros(n);B=sp.zeros(n)
for i in range(n):
 A[i,i]=1;A[i,(i+1)%n]=1
 for k in range(n):B[i,(i+k)%n]=(-1)**k
assert A*B==2*sp.eye(n) and B*A==2*sp.eye(n) and A.det()==2
ns={'__file__':str(P/'q0_exact_closure_radius.py')};exec((P/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0],ns)
xx=ns['x0'];r=math.exp(xx[-1]);ys=np.exp(xx[53:62]);al,w,cl,area=ns['calc'](xx);u=np.roll(ys,1);v=ys
L=np.arctan2(v*np.sin(al),u-v*np.cos(al));T=math.pi-al-L;tau=math.pi-T-np.roll(L,-1)-2*xx[33:42];ww=np.array(B).astype(float)@tau
ell=np.sqrt(u*u+v*v-2*u*v*np.cos(al));rr=2*np.sin(ww/2)/ell
errw=float(max(abs(ww-w)));errR=float(max(abs(rr-r)))
assert max(errw,errR)<1e-13
# Uniform intrinsic rescaling changes recovered R inversely; candidate shape unchanged.
scaleerrs=[]
for scale in [.7,.9,1.1]:scaleerrs.append(float(max(abs(2*np.sin(ww/2)/(scale*ell)-r/scale))))
assert max(scaleerrs)<1e-13
# Positive turns alone do not ensure positive odd-inverted widths: explicit rational control summing2pi.
t=sp.Matrix([sp.Rational(3,10)]+[sp.Rational(7,80)]*8)*2*sp.pi;wx=B*t;assert sum(t)==2*sp.pi and min(wx)<0 and max(t)<sp.pi
out={'matrix_det':int(A.det()),'exact_matrix_identity':'(I+shift)*alternating=2I','candidate_width_error':errw,'candidate_scale_error':errR,'candidate_radii_recovered':rr.tolist(),'candidate_radius':r,'scale_errors':scaleerrs,'scope':'exact matrix identity, numeric geometry calibration only'}
(P/'odd_scale_control.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
