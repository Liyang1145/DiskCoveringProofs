"""Directed interval subdivision test for d/delta of saturated face-1 branch.
This is a proof candidate only if every legal box is covered and all boxes certify positive.
"""
from interval_joint_patch import I,iv,pi,R,acos,lf,uf,clip,pos,z
import math,heapq,time,json
# constants
Z=z; a1=Z[1]-Z[9];a2=Z[3]-Z[9];q1=-Z[16];g1=-Z[78];q2=Z[20];g2=Z[82];zz=Z[3]-Z[1]
BMAX=acos(I(.375));LO=I(1);RLO=I(.375);RHI=I(.38)
def ev(x):
 r,b1,b2,de=x;s=iv.sqrt(1-r*r);A=b1-de;B=b2+de
 if A.b<=0 or B.b<=0:return None
 H=2*r*iv.sin(2*b1-de);dH=-2*r*iv.cos(2*b1-de)
 # necessary second-face cap and hub-norm disk; reject only certainly impossible
 H2=2*r*iv.sin(b2+B)
 if H.a>H2.b:return None
 v=H*iv.cos(de);t=H*iv.sin(de)
 norm=(v-s)*(v-s)+t*t-(1-r)*(1-r)
 if norm.a>0:return None
 S=iv.sin(b1)*iv.sin(A)+iv.sin(b2)*iv.sin(B)
 dS=-iv.sin(b1)*iv.cos(A)+iv.sin(b2)*iv.cos(B)
 dv=zz+dH*r*S+H*r*dS
 for i,(b,ang,dang,aa,qq,gg) in enumerate([(b1,A,-1,a1,q1,g1),(b2,B,1,a2,q2,g2)]):
  if i==0:
   e=r*iv.sin(ang)/R;de=r*iv.cos(ang)*dang/R;dp=I(0)
  else:
   Y=2*r*iv.sin(b)*iv.sin(ang);X=H-2*r*iv.sin(b)*iv.cos(ang);Q=X*X+Y*Y
   if Q.b<1/50000**2 or Q.a>4*.38**2:return None
   dY=2*r*iv.sin(b)*iv.cos(ang)*dang;dX=dH+2*r*iv.sin(b)*iv.sin(ang)*dang
   e=iv.sqrt(Q)/(2*R);de=(X*dX+Y*dY)/(2*R*iv.sqrt(Q));dp=(X*dY-Y*dX)/Q
  dv+=aa*dp+(2*qq*e+gg)*de
 return dv

def certify(nr=4,nb=12,nd=24):
 out=[];bad=[];cnt=0
 rs=[.375+(.38-.375)*i/nr for i in range(nr)];bs=[1+(float(BMAX.b)-1)*i/nb for i in range(nb)];ds=[-float(BMAX.b)+2*float(BMAX.b)*i/nd for i in range(nd)]
 for ir in range(nr):
  rr=I(rs[ir],rs[ir+1] if ir+1<nr else .38)
  for i in range(nb):
   b1=I(bs[i],bs[i+1] if i+1<nb else float(BMAX.b))
   for j in range(nb):
    b2=I(bs[j],bs[j+1] if j+1<nb else float(BMAX.b))
    for k in range(nd):
     de=I(ds[k],ds[k+1] if k+1<nd else float(BMAX.b))
     # intersect legal delta [-b2,b1] and require A,B positive
     dl=max(de.a,-b2.b);dh=min(de.b,b1.b)
     if dl>dh:continue
     x=ev([rr,b1,b2,I(dl,dh)]);cnt+=1
     if x is not None:
      if x.a<=0:bad.append({'box':[(float(v.a),float(v.b)) for v in [rr,b1,b2,I(dl,dh)]],'dv':str(x)})
      else:out.append(x.a)
 return {'boxes':cnt,'bad':bad[:20],'badcount':len(bad),'minlower':float(min(out)) if out else None}
if __name__=='__main__':
 t=time.time();o=certify();o['seconds']=time.time()-t;json.dump(o,open('face_deriv_probe.json','w'),indent=2);print(o)
