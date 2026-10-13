"""Directed interval subdivision proof candidate for dV/ddelta on face-2 saturated branch."""
from interval_joint_patch import I,iv,R,acos,z
import json,hashlib
from pathlib import Path
P=Path(__file__).parent; a1=z[1]-z[9];a2=z[3]-z[9];q1=-z[16];g1=-z[78];q2=z[20];g2=z[82];zz=z[3]-z[1]
def ev(x):
 r,b1,b2,de=x;s=iv.sqrt(1-r*r);A=b1-de;B=b2+de
 if A.b<=0 or B.b<=0:return None
 H=2*r*iv.sin(2*b2+de);dH=2*r*iv.cos(2*b2+de)
 if H.a>(2*r*iv.sin(b1+A)).b:return None
 v=H*iv.cos(de);t=H*iv.sin(de);norm=(v-s)*(v-s)+t*t-(1-r)*(1-r)
 if norm.a>0:return None
 S=iv.sin(b1)*iv.sin(A)+iv.sin(b2)*iv.sin(B);dS=-iv.sin(b1)*iv.cos(A)+iv.sin(b2)*iv.cos(B)
 dv=zz+dH*r*S+H*r*dS
 for i,(b,ang,dang,aa,qq,gg) in enumerate([(b1,A,-1,a1,q1,g1),(b2,B,1,a2,q2,g2)]):
  if i==1:e=r*iv.sin(ang)/R;de1=r*iv.cos(ang)*dang/R;dp=I(0)
  else:
   Y=2*r*iv.sin(b)*iv.sin(ang);X=H-2*r*iv.sin(b)*iv.cos(ang);Q=X*X+Y*Y
   if Q.b<1/50000**2 or Q.a>4*.38**2:return None
   dY=2*r*iv.sin(b)*iv.cos(ang)*dang;dX=dH+2*r*iv.sin(b)*iv.sin(ang)*dang
   e=iv.sqrt(Q)/(2*R);de1=(X*dX+Y*dY)/(2*R*iv.sqrt(Q));dp=(X*dY-Y*dX)/Q
  dv+=aa*dp+(2*qq*e+gg)*de1
 return dv
RLO=.375;RHI=.38;BLO=1.;BHI=1.1863995522992576;NR,NB,ND=4,12,24
stack=[]
for i in range(NR):
 r=I(RLO+(RHI-RLO)*i/NR,RLO+(RHI-RLO)*(i+1)/NR)
 for j in range(NB):
  b1=I(BLO+(BHI-BLO)*j/NB,BLO+(BHI-BLO)*(j+1)/NB)
  for k in range(NB):
   b2=I(BLO+(BHI-BLO)*k/NB,BLO+(BHI-BLO)*(k+1)/NB)
   for l in range(ND):
    d=I(-BHI+2*BHI*l/ND,-BHI+2*BHI*(l+1)/ND);lo=max(d.a,-b2.b);hi=min(d.b,b1.b)
    if lo<=hi:stack.append(([r,b1,b2,I(lo,hi)],0))
c={'initial':len(stack),'positive':0,'infeasible':0,'bisected':0,'remaining':0};minpos=1e9;md=0
while stack:
 x,dep=stack.pop();md=max(md,dep);v=ev(x)
 if v is None:c['infeasible']+=1;continue
 if v.b<0:c['positive']+=1;minpos=min(minpos,float(-v.b));continue
 if dep>=20:c['remaining']+=1;print('UNRESOLVED',[(float(y.a),float(y.b))for y in x],v);continue
 k=max(range(4),key=lambda i:float(x[i].b-x[i].a));m=(x[k].a+x[k].b)/2
 for side in [0,1]:y=x.copy();y[k]=I(x[k].a,m) if side==0 else I(m,x[k].b);stack.append((y,dep+1))
 c['bisected']+=1
out={'scope':'face2 saturated derivative high-bearing rectangular overbox','counts':c,'maxdepth':md,'min_positive_lower':minpos,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'status':'proved-interval' if c['remaining']==0 else 'unresolved'};json.dump(out,open(P/'face2_derivative_certificate.json','w'),indent=2);print(out)
