"""Direct rotated-coordinate interval dual for full hub-line boxes.
Numeric LP provides proposals only; certify() uses rational weights and iv.
Hub chart(s,x,y) maps to(x-s,y),(x+s,y), exposure centers pi,0.
"""
from fractions import Fraction as F
from pathlib import Path
import sys,json,math,time
import numpy as np
from scipy.optimize import linprog
from mpmath import iv
import onehub_interval_certificate as K
iv.dps=25
sys.path.insert(0,str(K.P/'members/two-hub/py'))
from dual2 import basis_arc,basis_arc_int
Q=K.Q;U=K.U;PI=iv.pi

def propose(s,x,y,order=4,nr=24,np_=120):
 u=float(K.Uq);b=math.acos(s/u);hs=[(x-s,y),(x+s,y)];es=[(math.pi,math.pi-b),(0,math.pi-b)]
 per=2*order+1
 req=np.concatenate([basis_arc(0,math.pi,True,order)]+[basis_arc(c,h,True,order) for c,h in es])
 rows=[]
 for rho in np.linspace(1-u,math.sqrt(1-u*u),nr):
  al=math.acos(max(-1,min(1,(1+rho*rho-u*u)/(2*rho))))
  for ph in np.linspace(0,2*math.pi,np_,endpoint=False):
   row=list(basis_arc(ph,al,True,order))
   for (hx,hy),(ce,he) in zip(hs,es):
    dx=rho*math.cos(ph)-hx;dy=rho*math.sin(ph)-hy;ell=math.hypot(dx,dy)
    v=np.zeros(per) if ell>=2*u else basis_arc_int(math.atan2(dy,dx),math.acos(ell/(2*u)),ce,he,True,order)
    row.extend(v)
   rows.append(row)
 A=np.array(rows)
 # Generator densities 1,1+cos(k),1-cos(k),1+sin(k),1-sin(k).
 gen=[]
 for block in range(3):
  v=np.zeros(3*per);v[block*per]=1;gen.append(v)
  for j in range(1,per):
   for sign in [-1,1]:
    v=np.zeros(3*per);v[block*per]=1;v[block*per+j]=sign;gen.append(v)
 G=np.array(gen).T;AG=A@G;rg=req@G
 obj=np.zeros(G.shape[1]+1);obj[-1]=1
 res=linprog(obj,A_ub=np.column_stack([AG,-np.ones(len(A))]),b_ub=np.zeros(len(A)),A_eq=[np.r_[rg,0]],b_eq=[1],bounds=[(0,None)]*len(obj),method='highs',options={'threads':1})
 if not res.success:raise RuntimeError(res.message)
 # Rationalize generator coefficients, so nonnegativity survives automatically.
 qgen=[F(round(float(v)*10**8),10**8) for v in res.x[:-1]]
 flat=[sum(F(int(G[i,j]))*qgen[j] for j in range(len(qgen))) for i in range(3*per)]
 return {'weights':[[str(v) for v in flat[i*per:(i+1)*per]] for i in range(3)],'numeric_max':float(res.fun),'order':order,'hubpoint':[s,x,y]}

class Certificate:
 def __init__(self,H,W):
  self.H=H;self.W=[[Q(v) for v in row] for row in W];self.order=(len(W[0])-1)//2
  for row in W:assert F(row[0])>=sum(abs(F(v)) for v in row[1:])
  s,x,y=[K.box(*p) for p in H]
  assert s.a>0 and s.b<U.a
  self.hs=[(x-s,y),(x+s,y)]
  b=K.acos01(s/U);self.es=[(PI,PI-b),(iv.mpf(0),PI-b)]
  self.req=2*PI*self.W[0][0]
  for j,(w,(ce,he)) in enumerate(zip(self.W[1:],self.es)):
   val=2*w[0]*he
   for k in range(1,self.order+1):val+=2*w[k]*((-1)**k if j==0 else 1)*iv.sin(k*he)/k
   self.req+=val
  self.target=self.req/10
 def primitive(self,w,t):
  ans=w[0]*t;n=self.order
  for k in range(1,n+1):ans+=w[k]*iv.sin(k*t)/k-w[n+k]*iv.cos(k*t)/k
  return ans
 def arc(self,w,center,half):
  ans=2*w[0]*half;n=self.order
  for k in range(1,n+1):ans+=2*iv.sin(k*half)/k*(w[k]*iv.cos(k*center)+w[n+k]*iv.sin(k*center))
  return ans
 def integral_outer(self,w,lo,hi):
  # F increasing by nonnegative density; integrate containing endpoints.
  if hi.b<=lo.a:return iv.mpf(0)
  return self.primitive(w,hi.b)-self.primitive(w,lo.a)
 def upper(self,B):
  z=K.box(*B[0]);rho=K.rl+(K.rh-K.rl)*z
  pl,pr=B[1];ph=2*PI*K.box(pl,pr);ph0=2*PI*Q((pl+pr)/2)
  half=2*PI*K.box((pl-pr)/2,(pr-pl)/2)
  q=(1+rho*rho-U*U)/(2*rho);al=K.acos01(q)
  # Direct Fourier arc integral avoids subtracting unrelated constants.
  w=self.W[0];ans=2*w[0]*al;n=self.order
  for k in range(1,n+1):ans+=2*iv.sin(k*al)/k*(w[k]*iv.cos(k*ph)+w[n+k]*iv.sin(k*ph))
  c0=iv.cos(ph0);s0=iv.sin(ph0)
  for w,(hx,hy),(ce,he) in zip(self.W[1:],self.hs,self.es):
   X=rho*iv.cos(half)-hx*c0-hy*s0
   Y=rho*iv.sin(half)+hx*s0-hy*c0
   ell=iv.sqrt(X**2+Y**2)
   if ell.a>=(2*U).b:continue
   # A containing angular wedge around ph0; no corner/extremum/lift heuristics.
   if X.a<=0:return None
   psi=ph0+iv.atan2(Y,X)
   q=ell/(2*U);q=iv.mpf([min(q.a,iv.mpf(1)),min(q.b,iv.mpf(1))]);be=K.acos01(q)
   EL=ce-he;ER=ce+he
   # If one lift of the entire ring arc lies in the exposed arc for all
   # parameters, exact whole-arc formula is far tighter than enlarged endpoints.
   full=False
   for shift in range(-2,3):
    cen=psi+2*shift*PI
    if (cen-be).a>=EL.b and (cen+be).b<=ER.a:
     ans+=self.arc(w,psi,be);full=True;break
   if full:continue
   for shift in range(-2,3):
    aa=psi-be+2*shift*PI;bb=psi+be+2*shift*PI
    lo=iv.mpf([max(EL.a,aa.a),max(EL.b,aa.b)])
    hi=iv.mpf([min(ER.a,bb.a),min(ER.b,bb.b)])
    ans+=self.integral_outer(w,lo,hi)
  return ans
 def certify(self,budget=100000):
  stack=[((F(0),F(1)),(F(0),F(1)))];n=leaf=0;worst=iv.mpf(0)
  while stack:
   B=stack.pop();n+=1
   if n>budget:return {'status':'budget','boxes':n,'pending':len(stack)+1}
   try:v=self.upper(B)
   except ValueError:v=None
   if v is not None and v.b<self.target.a:
    leaf+=1;worst=max(worst,v.b);continue
   widths=[float(B[0][1]-B[0][0]),6*float(B[1][1]-B[1][0])];j=int(widths[1]>widths[0]);a,b=B[j];m=(a+b)/2
   if b-a<F(1,2**24):return {'status':'unresolved','box':str(B),'upper':str(v),'target':str(self.target)}
   for pair in [(a,m),(m,b)]:
    child=list(B);child[j]=pair;stack.append(tuple(child))
  return {'status':'certified','boxes':n,'leaves':leaf,'upper':str(worst),'target':str(self.target)}

if __name__=='__main__':
 s=F(1,5);x=F(0);y=F(1,80);eps=F(sys.argv[1]) if len(sys.argv)>1 else F(0)
 H=[(s-eps,s+eps),(x,x+eps),(max(F(0),y-eps),y+eps)]
 t=time.time();p=propose(float(s),float(x),float(y));print('proposal',p['numeric_max'],'time',time.time()-t,flush=True)
 C=Certificate(H,p['weights']);out=C.certify();out.update({'proposal':p,'H':[[str(v) for v in r] for r in H],'seconds':time.time()-t})
 print(json.dumps(out),flush=True)
 (K.P/'evidence'/('hubline-point-'+str(eps).replace('/','-')+'.json')).write_text(json.dumps(out,indent=2))
