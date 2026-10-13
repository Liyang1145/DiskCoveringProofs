"""C861 highbearing3outer+widthscalar+3circlearc supremum; necessary filters only."""
import interval_cartesian_cancel as base
import interval_patch_delta as fibers
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,pi,lf,uf,pos,clip

def setup(outer):
 r,b1,b2=outer;s=iv.sqrt(1-r*r)
 st=base.setup([r,b1,b2,I('.3','.76')])
 if st is None:return None
 K,fs=st;disks=[(r*iv.sin(2*b1),-r*iv.cos(2*b1),r),(r*iv.sin(2*b2),r*iv.cos(2*b2),r),(s,I(0),1-r)]
 def circle(theta,j):
  cx,cy,rho=disks[j];v=cx+rho*iv.cos(theta);t=cy+rho*iv.sin(theta)
  if v.b<=0:return None
  for i,(dx,dy,rr)in enumerate(disks):
   if i==j:continue
   if ((v-dx)**2+(t-dy)**2-rr*rr).a>0:return None
  if (t+v*iv.tan(b2)).b<0 or (v*iv.tan(b1)-t).b<0:return None
  ans=r*(iv.sin(b1)**2+iv.sin(b2)**2)*v+r*(iv.sin(b2)*iv.cos(b2)-iv.sin(b1)*iv.cos(b1))*t
  for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
   Y=2*r*iv.sin(b)**2+sg*t;X=v-r*iv.sin(2*b)
   if Y.b<0:return None
   Y=pos(Y);Q=clip(X*X+Y*Y,I(1)/50000**2,4*r*r)
   if Q is None:return None
   ee=iv.sqrt(Q)/(2*R);ans+=a*iv.atan2(Y,X)+k.quad_range(bb,gg,ee)
  return ans
 return K,fs[:2],[(lambda th,j=j:circle(th,j),(lf(-pi),uf(pi)))for j in range(3)]

def bound(outer,tol=1e-5,maxeval=129):
 # Caller MUSTcoveronlyC861outerdomain b>=1; no silentprojection.
 assert all(b.a>=1 for b in outer[1:])
 st=setup(outer)
 if st is None:return None
 K,ws,cs=st;ww=[fibers.envelope(f,dom,tol,maxeval)for f,dom in ws];cc=[fibers.envelope(f,dom,tol,maxeval)for f,dom in cs]
 if any(row['upper']==-float('inf')for row in ww)or all(row['upper']==-float('inf')for row in cc):return None
 total=K+sum((I(row['upper'])for row in ww),I(0))+I(max(row['upper']for row in cc))
 return {'upper':uf(total),'widths':ww,'circles':cc}
