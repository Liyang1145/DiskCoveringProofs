"""Smooth full component AD for rank-one tangent ridge bound. Exact rational tau=87/40.
Uses full analytic extension for MVT, never physical clipping in derivatives.
"""
from patch_smooth_jet import Jet,Unsafe,sin,cos,sqrt,atan2,asin
from interval_joint_patch import I,iv,R,z,pi,uf
TAU=I(87)/40

def component(box,j):
 r,b,w=[Jet(x,[I(int(i==k))for k in range(7)])for i,x in enumerate(box)]
 s=sqrt(1-r*r);ph=asin(r);x0=2*b-pi/2+ph;p=cos(w)-r*cos(x0+w);x=-sin(w)+r*sin(x0+w)
 cx=s-2*r*sin(b)*cos(b);cy=-2*r*sin(b)**2;px=s*cos(w)-r*sin(w);py=-s*sin(w)-r*cos(w)
 q=(px-cx)**2+(py-cy)**2;den=1-p
 cn=1+r.v*r.v-2*r.v*iv.cos(x0.v)
 if cn.a>=0 and cn.b<1:
  gap=1-iv.sqrt(cn);den.v=I(max(den.v.a,gap.a),den.v.b);q.v=I(max(q.v.a,(gap**2).a),q.v.b)
 u=sqrt(q)/R;eta=atan2(x,den)
 mu,h,d,l=(z[1],z[112],z[34],z[96])if j==0 else(z[3],z[115],z[39],z[101])
 val=-r*s*sin(b)**2+Jet(I(1)/2-mu)*w+x/2+Jet(mu+h)*eta-Jet(d)*u*u-Jet(l)*u
 bb,gg,aa=(z[20],z[82],z[3]-z[9])if j==0 else(-z[16],-z[78],z[1]-z[9])
 e=r*sin(b)/R
 val+=r*r*sin(2*b)+Jet(aa)*b+Jet(bb)*e*e+Jet(gg)*e-2*r*r*Jet(iv.cos(2*TAU))*b
 return val,q

def bound(box,j):
 if (iv.cos(box[1])-box[0]).b<0:return None
 try:
  f,q=component(box,j)
  if (q.v-box[0]**2).a>0:return None
  mid=[I((float(x.a)+float(x.b))/2)for x in box];fc,_=component(mid,j)
  mv=fc.v+sum((d*(x-m)for d,x,m in zip(f.d,box,mid)),I(0))
  return min(uf(f.v),uf(mv)),[uf(abs(d))for d in f.d[:3]]
 except Unsafe:return float('inf'),[1,1,1]

def constant(r):
 return pi*(z[113]+z[114]-z[2])+pi/2*(z[112]+z[115]-z[1]-z[3])+(1-z[1]-z[3])*asin(Jet(r)).v+r*r*(-iv.sin(2*TAU)+2*TAU*iv.cos(2*TAU))
