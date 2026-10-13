"""C861/C862 boundarycover with exactsaturatedface identities; experimental."""
import interval_hub_boundary as base
import interval_patch_delta as fibers
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,pi,lf,uf,clip,pos

def setup(outer):
 st=base.setup(outer)
 if st is None:return None
 K,ws,_=st;r,b1,b2=outer;s=iv.sqrt(1-r*r)
 def branch(de,j):
  A=clip(b1-de,0,pi);B=clip(b2+de,0,pi)
  if A is None or B is None:return None
  if j==0:H=2*r*iv.sin(b1+A)
  elif j==1:H=2*r*iv.sin(b2+B)
  else:
   rad=(1-r)**2-s*s*iv.sin(de)**2
   if rad.b<0:return None
   H=s*iv.cos(de)+(1 if j==2 else -1)*iv.sqrt(pos(rad))
  H=clip(H,s-(1-r),2*r)
  if H is None:return None
  if (H-2*r*iv.sin(b1+A)).a>0 or (H-2*r*iv.sin(b2+B)).a>0:return None
  if (H*H-2*s*iv.cos(de)*H+2*r*(1-r)).a>0:return None
  ans=(z[3]-z[1])*de+H*r*(iv.sin(b1)*iv.sin(A)+iv.sin(b2)*iv.sin(B))
  for i,(b,ang,a,bb,gg)in enumerate([(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]):
   if j==i:
    e=r*iv.sin(ang)/R;phi=b
   else:
    Y=2*r*iv.sin(b)*iv.sin(ang);X=H-2*r*iv.sin(b)*iv.cos(ang)
    Q=clip(X*X+Y*Y,I(1)/50000**2,4*r*r)
    if Q is None:return None
    e=iv.sqrt(Q)/(2*R);phi=iv.atan2(Y,X)
   ans+=a*phi+k.quad_range(bb,gg,e)
  return ans
 dom=(lf(-b2),uf(b1));return K,ws,[(lambda de,j=j:branch(de,j),dom)for j in range(4)]
def bound(outer,tol=1e-5,maxeval=129):
 assert all(b.a>=1 for b in outer[1:])
 st=setup(outer)
 if st is None:return None
 K,ws,cs=st;ww=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in ws];cc=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in cs]
 if any(row['upper']==-float('inf')for row in ww)or all(row['upper']==-float('inf')for row in cc):return None
 total=K+sum((I(row['upper'])for row in ww),I(0))+I(max(row['upper']for row in cc))
 return {'upper':uf(total),'widths':ww,'branches':cc}
