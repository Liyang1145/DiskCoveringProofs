"""Ridge full-extension outer MVT bound. Width domains fixed across each outer box."""
from cartesian_full_jet import parts as oldparts
from patch_smooth_jet import Jet,Unsafe,sin
from interval_joint_patch import I,R,z,iv
import interval_patch_delta as fibers
def parts(outer):
 K,fs=oldparts(outer+[I(0)])
 r,b1,b2=[Jet(x,[I(int(i==j))for j in range(7)])for i,x in enumerate(outer)]
 d=b1-b2;hub=Jet(z[3]-z[1])*d+4*r*r*sin(b1+b2)*sin(b1)*sin(b2)+Jet(z[1]-z[9])*b1+Jet(z[3]-z[9])*b2
 e1=r*sin(b2)/R;e2=r*sin(b1)/R
 hub+=-Jet(z[16])*e1*e1-Jet(z[78])*e1+Jet(z[20])*e2*e2+Jet(z[82])*e2
 return K+hub,fs[:2]
def mean(outer,domains,n=8):
 K,fs=parts(outer);mid=[I((float(x.a)+float(x.b))/2)for x in outer];Km,fm=parts(mid);grad=K.d[:3];up=Km.v
 for f,fc,(lo,hi) in zip(fs,fm,domains):
  vals=[f(I(lo+(hi-lo)*j/n,hi if j==n-1 else lo+(hi-lo)*(j+1)/n))for j in range(n)]
  for k in range(3):grad[k]+=I(min(v.d[k].a for v in vals),max(v.d[k].b for v in vals))
  up+=I(fibers.envelope(lambda x:fc(x).v,(lo,hi),1e-5,65)['upper'])
 return up+sum((g*(x-m)for g,x,m in zip(grad,outer,mid)),I(0)),grad
