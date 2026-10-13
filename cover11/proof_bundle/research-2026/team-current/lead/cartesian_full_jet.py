"""Unfiltered smooth Cartesian7objective; derivativeguards over full rectangular extension."""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt,atan2,asin
from interval_joint_patch import I,R,z,pi

def parts(outer):
 # Return K and scalarfunctions Jet(y) but yhaszeroouterderivatives.
 js=[Jet(x,[I(int(i==j))for j in range(7)])for i,x in enumerate(outer)];r,b1,b2,v=js;s=sqrt(1-r*r);phi=asin(r)
 K=Jet(pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3]))+Jet(1-z[1]-z[3])*phi
 def width(w,b,mu,h,d,l):
  w=Jet(w);x0=2*b-pi/2+phi;p=cos(w)-r*cos(x0+w);x=-sin(w)+r*sin(x0+w)
  # Cartesian sum-of-squares provides same analyticq without cancellation.
  cx=s-2*r*sin(b)*cos(b);cy=-2*r*sin(b)**2;px=s*cos(w)-r*sin(w);py=-s*sin(w)-r*cos(w)
  q=(px-cx)**2+(py-cy)**2;den=1-p
  # Exact unitP reverse-triangle guard holds on the ENTIRE extension,
  # not a physicalfeasibility clip: cn=|c|^2 from trig identity.
  from interval_joint_patch import iv
  cn=1+r.v*r.v-2*r.v*iv.cos(x0.v)
  if cn.a>=0 and cn.b<1:
   gap=1-iv.sqrt(cn);den.v=I(max(den.v.a,gap.a),den.v.b);q.v=I(max(q.v.a,(gap**2).a),q.v.b)
  if den.v.a<=0:raise Unsafe('eta denominator')
  u=sqrt(q)/R;eta=atan2(x,den)
  return -r*s*sin(b)**2+Jet(I(1)/2-mu)*w+x/2+Jet(mu+h)*eta-Jet(d)*u*u-Jet(l)*u
 def hub(t):
  t=Jet(t);ans=r*(sin(b1)**2+sin(b2)**2)*v+r*(sin(b2)*cos(b2)-sin(b1)*cos(b1))*t
  for b,sg,a,bb,gg in [(b1,-1,z[1]-z[9],-z[16],-z[78]),(b2,1,z[3]-z[9],z[20],z[82])]:
   sb=sin(b);cb=cos(b);Y=2*r*sb*sb+sg*t;X=v-2*r*sb*cb;Q=X*X+Y*Y;ell=sqrt(Q)/(2*R)
   ans+=Jet(a)*atan2(Y,X)+Jet(bb)*ell*ell+Jet(gg)*ell
  return ans
 return K,[lambda w:width(w,b1,z[1],z[112],z[34],z[96]),lambda w:width(w,b2,z[3],z[115],z[39],z[101]),hub]

def outer_mean(outer,domains,n=8):
 """Whole-extension derivativehulls on scalarpartition, centerunfiltered maxenvelopes."""
 import interval_patch_delta as fibers
 K,fs=parts(outer);mids=[I((float(x.a)+float(x.b))/2)for x in outer];Km,fm=parts(mids)
 grad=K.d[:4];total=Km.v
 for fun,center,dom in zip(fs,fm,domains):
  lo,hi=dom;vs=[]
  for j in range(n):
   a=lo+(hi-lo)*j/n;b=hi if j==n-1 else lo+(hi-lo)*(j+1)/n
   vs.append(fun(I(a,b)))
  for k in range(4):grad[k]+=I(min(v.d[k].a for v in vs),max(v.d[k].b for v in vs))
  up=fibers.envelope(lambda y:center(y).v,dom,1e-5,31)['upper'];total+=I(up)
 return total+sum((d*(x-m)for d,x,m in zip(grad,outer,mids)),I(0)),grad
