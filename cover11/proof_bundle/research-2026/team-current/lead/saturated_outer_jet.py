"""Full extension AD for two saturatedface branches; outer(r,b1,b2), scalar(w1,w3,de)."""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt,atan2,asin
from interval_joint_patch import I,R,z,pi,iv
from cartesian_full_jet import parts as oldparts

def parts(outer,j):
 K,ws=oldparts(outer+[I(0)])
 r,b1,b2=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(outer)]
 def hub(de):
  de=Jet(de);A=b1-de;B=b2+de;H=2*r*sin(b1+A)if j==0 else 2*r*sin(b2+B)
  ans=Jet(z[3]-z[1])*de+H*r*(sin(b1)*sin(A)+sin(b2)*sin(B))
  for i,(b,ang,a,bb,gg)in enumerate([(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]):
   if i==j:e=r*sin(ang)/R;phi=b
   else:
    X=H-2*r*sin(b)*cos(ang);Y=2*r*sin(b)*sin(ang);e=sqrt(X*X+Y*Y)/(2*R);phi=atan2(Y,X)
   ans+=Jet(a)*phi+Jet(bb)*e*e+Jet(gg)*e
  return ans
 return K,ws[:2]+[hub]

def mean(outer,domains,j,n=8):
 import interval_patch_delta as fibers
 K,fs=parts(outer,j);mid=[I((float(x.a)+float(x.b))/2)for x in outer];Km,fm=parts(mid,j);grad=K.d[:3];upper=Km.v
 for f,fc,(lo,hi)in zip(fs,fm,domains):
  vals=[f(I(lo+(hi-lo)*k/n,hi if k==n-1 else lo+(hi-lo)*(k+1)/n))for k in range(n)]
  for k in range(3):grad[k]+=I(min(v.d[k].a for v in vals),max(v.d[k].b for v in vals))
  upper+=I(fibers.envelope(lambda x:fc(x).v,(lo,hi),1e-5,65)['upper'])
 return upper+sum((d*(x-m)for d,x,m in zip(grad,outer,mid)),I(0)),grad
