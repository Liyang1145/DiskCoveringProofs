"""Atomic two-circle/exposed-circle dual. Bearing arithmetic uses only IEEE754
basic operations followed by nextafter outward; no transcendental float bounds.
Atom positions/weights are exact rational proposals. Integer capture sums exact.
Ring centers are dyadic cartesian boxes; annulus filtered by outward squares.
"""
from fractions import Fraction as F
import numpy as np,math,json,time,sys
from pathlib import Path
import hubline_capacity as H
P=H.K.P;U=H.K.Uq
NEG=-np.inf;POS=np.inf

def bounds(q):
 q=F(q);v=float(q);f=F.from_float(v)
 return (np.nextafter(v,NEG) if f>q else v,np.nextafter(v,POS) if f<q else v)
def add(A,B):return np.nextafter(A[0]+B[0],NEG),np.nextafter(A[1]+B[1],POS)
def sub(A,B):return np.nextafter(A[0]-B[1],NEG),np.nextafter(A[1]-B[0],POS)
def square(A):
 al,ah=A
 lo=np.where(al>0,al,np.where(ah<0,ah,0.0));hi=np.maximum(np.abs(al),np.abs(ah))
 return np.maximum(0,np.nextafter(lo*lo,NEG)),np.nextafter(hi*hi,POS)
def norm2(X,Y):return add(square(X),square(Y))
def units(N):
 # A proposal angle rounded to rational stereographic parameter gives an EXACT
 # point of S1. No closeness to a uniform grid is used in the proof.
 ans=[]
 for j in range(N):
  if 2*j==N:ans.append((F(-1),F(0)));continue
  t=F(round(math.tan(math.pi*j/N)*10**8),10**8)
  ans.append(((1-t*t)/(1+t*t),2*t/(1+t*t)))
 return ans

def build_atoms(Hbox,weights,N=512):
 sl,sh=Hbox[0];xl,xh=Hbox[1];yl,yh=Hbox[2]
 C=units(N);X=[];Y=[];W=[];records=[]
 n=(len(weights[0])-1)//2
 def weight(w,c,s):
  # Complex powers exact rational; weight rounded to positive integer is a
  # new atomic measure, not an approximation invoked as a premise.
  v=F(w[0]);co=F(1);si=F(0)
  for k in range(1,n+1):
   co,si=co*c-si*s,si*c+co*s
   v+=F(w[k])*co+F(w[n+k])*si
  assert v>=0
  return round(v*10**9)
 for j,w in enumerate(weights):
  for c,s in C:
   if j==1 and U*c>sl:continue
   if j==2 and U*c < -sl:continue
   wt=weight(w,c,s)
   if not wt:continue
   if j==0:xx=(c,c);yy=(s,s)
   elif j==1:xx=(xl-sh+U*c,xh-sl+U*c);yy=(yl+U*s,yh+U*s)
   else:xx=(xl+sl+U*c,xh+sh+U*c);yy=(yl+U*s,yh+U*s)
   X.append((bounds(xx[0])[0],bounds(xx[1])[1]));Y.append((bounds(yy[0])[0],bounds(yy[1])[1]));W.append(wt)
   records.append([j,str(c),str(s),wt])
 a=np.array(X);b=np.array(Y);ww=np.array(W,dtype=np.int64)
 assert sum(W)<2**60
 return (a[:,0],a[:,1]),(b[:,0],b[:,1]),ww,records

class Atoms:
 def __init__(self,Hbox,weights,N=512):
  self.Hbox=Hbox;self.X,self.Y,self.W,self.records=build_atoms(Hbox,weights,N)
  self.total=int(self.W.sum());self.r2=bounds(U*U);self.inner=bounds((1-U)**2);self.outer=bounds(1-U*U)
 def bound(self,B):
  cx=(B[0],B[1]);cy=(B[2],B[3]);rad=norm2(cx,cy)
  if rad[1]<self.inner[0] or rad[0]>self.outer[1]:return -1
  dx=sub(cx,self.X);dy=sub(cy,self.Y);d2=norm2(dx,dy)
  possible=d2[0]<=self.r2[1]
  return int(self.W[possible].sum())
 def certify(self,budget=2000000):
  stack=[(-1.,1.,-1.,1.)];n=leaves=outside=0;worst=0
  while stack:
   B=stack.pop();n+=1
   if n>budget:return {'status':'budget','boxes':n,'pending':len(stack)+1}
   val=self.bound(B)
   if val<0:outside+=1;continue
   if 10*val<self.total:leaves+=1;worst=max(worst,val);continue
   a,b,c,d=B
   if max(b-a,d-c)<2**-22:return {'status':'unresolved','box':B,'cap':val,'total':self.total,'boxes':n}
   if b-a>=d-c:
    m=(a+b)/2;stack.extend([(a,m,c,d),(m,b,c,d)])
   else:
    m=(c+d)/2;stack.extend([(a,b,c,m),(a,b,m,d)])
  return {'status':'certified','boxes':n,'leaves':leaves,'outside':outside,'max_integer_capture':worst,'total_integer_demand':self.total,'gap_integer':self.total-10*worst,'atoms':len(self.W)}
if __name__=='__main__':
 eps=F(sys.argv[1]) if len(sys.argv)>1 else F(1,200);N=int(sys.argv[2]) if len(sys.argv)>2 else 512
 s=F(1,5);x=F(0);y=F(1,80);HB=[(s-eps,s+eps),(x,x+eps),(y-eps,y+eps)]
 source=json.loads((P/'evidence/hubline-point-0.json').read_text());W=source['proposal']['weights']
 t=time.time();C=Atoms(HB,W,N);print('atoms',len(C.W),'build',time.time()-t,flush=True)
 out=C.certify();out.update({'seconds':time.time()-t,'H':[[str(v) for v in r] for r in HB],'weights':W,'N':N,'atom_records':C.records})
 print(json.dumps({k:v for k,v in out.items() if k not in ('atom_records','weights')}),flush=True)
 (P/'evidence'/('hubline-atoms-'+str(eps).replace('/','-')+'-'+str(N)+'.json')).write_text(json.dumps(out,indent=2))
