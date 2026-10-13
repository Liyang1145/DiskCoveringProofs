"""Exact quadratic identities and coordinate calibration for flat-sector hubpatch."""
from pathlib import Path
import sympy as S,math,random,json,numpy as np
P=Path(__file__).parent;r,H,b,A=S.symbols('r H b A',real=True)
poly=H*H+(2*r*S.sin(b))**2-4*r*H*S.sin(b)*S.cos(A)-4*r*r*S.sin(A)**2
assert S.trigsimp(S.expand_trig(poly-(H-2*r*S.sin(b-A))*(H-2*r*S.sin(b+A))))==0
rng=random.Random(1111);n=0;err=0
for _ in range(10000):
 r=rng.uniform(.375,.38);b1=rng.uniform(.01,1.1);b2=rng.uniform(.01,1.1);A=rng.uniform(.001,b1+b2-.001);B=b1+b2-A;delta=b1-A;s=math.sqrt(1-r*r);disc=s*s*math.cos(delta)**2-2*r*(1-r)
 if disc<0:continue
 lo=max(2*r*abs(math.sin(delta)),s*math.cos(delta)-math.sqrt(disc));hi=min(2*r*math.sin(b1+A),2*r*math.sin(b2+B),s*math.cos(delta)+math.sqrt(disc))
 if hi<lo or hi<=0:continue
 H=rng.uniform(lo,hi);c2=np.array([s,0]);c1=c2+2*r*math.sin(b1)*np.array([-math.cos(b1),-math.sin(b1)]);c3=c2+2*r*math.sin(b2)*np.array([-math.cos(b2),math.sin(b2)]);hub=c2+H*np.array([-math.cos(delta),-math.sin(delta)])
 assert np.linalg.norm(hub)<=1-r+1e-12
 for c,a,bb in [(c1,A,b1),(c3,B,b2)]:
  u=c-c2;v=hub-c2;actual=math.atan2(abs(u[0]*v[1]-u[1]*v[0]),u@v);err=max(err,abs(actual-a));assert abs(actual-a)<1e-11
  pts=np.array([hub,c,c2]);cc=np.linalg.solve(2*(pts[1:]-pts[0]),(pts[1:]**2).sum(1)-(pts[0]**2).sum());rad=np.linalg.norm(cc-pts[0]);formula=math.sqrt(H*H+(2*r*math.sin(bb))**2-4*r*H*math.sin(bb)*math.cos(a))/(2*math.sin(a));err=max(err,abs(rad-formula));assert rad<=r+1e-10
 n+=1
out={'quadratic_factorization_exact':True,'coordinate_patches':n,'max_error':err,'scope':'analyticrootproof + offcandidatecoordinatecontrol; notglobalcertificate'}
(P/'hub_patch_control.json').write_text(json.dumps(out,indent=2));print(out)
