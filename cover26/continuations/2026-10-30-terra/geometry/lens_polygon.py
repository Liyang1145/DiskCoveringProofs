from fractions import Fraction as F
U=F(234700091,10**9)
D=[(1,0),(0,1),(F(3,5),F(4,5)),(F(4,5),F(3,5))]
D=list({(F(x)*sx,F(y)*sy) for a,b in D for x,y in ((a,b),(b,a)) for sx in (-1,1) for sy in (-1,1)})
def clip(poly,a,b,c):
 out=[]
 for p,q in zip(poly,poly[1:]+poly[:1]):
  A=a*p[0]+b*p[1]-c;B=a*q[0]+b*q[1]-c
  if A<=0:out.append(p)
  if (A<0 and B>0) or (A>0 and B<0):
   t=A/(A-B);out.append((p[0]+t*(q[0]-p[0]),p[1]+t*(q[1]-p[1])))
 return out
def coslo(x):return 1-x*x/2+x**4/24-x**6/720
def coshi(x):return 1-x*x/2+x**4/24
def sinlo(x):return x-x**3/6
def sinhi(x):return x-x**3/6+x**5/120
def lens(lo,hi,side):
 # a=(cos(2δ)-1, side sin(2δ)). Enclose all angles in interval.
 ax=(coslo(2*hi)-1,coshi(2*lo)-1); sy=(sinlo(2*lo),sinhi(2*hi)); ay=sy if side==1 else (-sy[1],-sy[0])
 p=[(-U,-U),(U,-U),(U,U),(-U,U)]
 for x,y in D:
  p=clip(p,x,y,U)
  sup=x*(ax[1] if x>=0 else ax[0])+y*(ay[1] if y>=0 else ay[0])
  p=clip(p,x,y,U+sup)
 p=clip(p,1,0,0)
 return p
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def bound(lo,hi,l2,h2):
 L=lens(lo,hi,-1);R=lens(l2,h2,1)
 return min(U*U,max(abs(cross(a,b)) for a in L for b in R))
if __name__=='__main__':
 for lo,hi in [(F(3,50),F(237,1000)),(F(1,5),F(237,1000)),(F(11,50),F(237,1000)),(F(23,100),F(237,1000))]:
  print(float(lo),float(hi),float(bound(lo,hi,lo,hi)),float(U*U))
