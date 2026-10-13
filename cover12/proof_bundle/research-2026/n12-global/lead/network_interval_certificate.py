"""Exact rational interval certificate for a fixed finite graph and rational stress.
Independent of root isolation or numerical optimization success. Numeric output only
proposes weights, feasible simplex reference y, and a negative-curvature allowance.
"""
from stress_interval import I,F
from network_graph import triangle,network_edges
from pathlib import Path
from math import factorial
import json,sys
P=Path(__file__).resolve().parents[1]
U=F('0.361102963744508672616920293904')

def trig(x,kind):
 x=I(x);maxx=max(abs(x.lo),abs(x.hi));assert maxx<7
 N=40;out=I(0);term=x if kind=='sin' else I(1)
 for k in range(N):
  degree=2*k+(1 if kind=='sin' else 0)
  out+=term
  term=-term*x*x/I((degree+1)*(degree+2))
 # Taylor through degree79 sin or78 cos; derivative bounded1.
 degree=2*N+(0 if kind=='sin' else -1)
 err=maxx**degree/F(factorial(degree))
 return out+I(-err,err)

def constants():
 def atan(x,N):
  s=sum(((-1)**k)*x**(2*k+1)/F(2*k+1) for k in range(N))
  nxt=((-1)**N)*x**(2*N+1)/F(2*N+1)
  return I(min(s,s+nxt),max(s,s+nxt))
 pi=16*atan(F(1,5),65)-4*atan(F(1,239),20)
 lo=F('0.73890078601154577911406246025920')
 hi=F('0.73890078601154577911406246025960')
 assert trig(I(lo/2),'sin').hi<U<trig(I(hi/2),'sin').lo
 L=I(lo,hi);D=9*L-2*pi
 assert 4*L.hi<pi.lo and D.lo>0
 return pi,L,D

def verify(data,kappa):
 blocks=data.get('blocks');faces=data['faces'] if 'faces' in data else triangle(blocks);nf,edges=network_edges(faces)
 # Round proposal to positive exact rational weights, THEN normalize exactly.
 if 'rational_weights' in data:
  alpha=[F(x) for x in data['rational_weights']]
 else:
  raw=[max(1,round(float(x)*10**10)) for x in data['weights']]
  alpha=[F(x,sum(raw)) for x in raw]
 assert len(alpha)==len(edges) and all(x>0 for x in alpha) and sum(alpha)==1
 size=nf+9
 Lap=[[I(0) for _ in range(size)] for _ in range(size)]
 for (i,j),w in zip(edges,alpha):
  w=I(w);Lap[i][i]+=w;Lap[j][j]+=w;Lap[i][j]-=w;Lap[j][i]-=w
 piv=[]
 for k in range(nf):
  p=Lap[k][k];assert p.lo>0;piv.append(p.dump())
  for i in range(k+1,size):
   for j in range(i,size):
    v=Lap[i][j]-Lap[i][k]*Lap[k][j]/p;Lap[i][j]=v;Lap[j][i]=v
 q={}
 for i in range(9):
  for j in range(i+1,9):
   q[i,j]=-Lap[nf+i][nf+j];assert q[i,j].lo>=0
 c=1-2*U*U;cs=[F(1),c]
 for d in range(2,5):cs.append(2*c*cs[-1]-cs[-2])
 M=[[I(0) for _ in range(9)] for _ in range(9)]
 for (i,j),qq in q.items():
  v=2*qq*I(cs[min(j-i,9-(j-i))]);M[i][i]+=v;M[j][j]+=v;M[i][j]-=v;M[j][i]-=v
 # Certify H>=M>=-kappa I (all mixed directions) using9x9 LDL.
 for i in range(9):M[i][i]+=I(kappa)
 mp=[]
 for k in range(9):
  p=M[k][k];assert p.lo>0,('M+kappaI pivot',k,p.dump());mp.append(p.dump())
  for i in range(k+1,9):
   for j in range(i,9):
    v=M[i][j]-M[i][k]*M[k][j]/p;M[i][j]=v;M[j][i]=v
 pi,L,D=constants()
 # Any exact simplex point is legal, even if numerical optimizer's output wasn't.
 if 'simplex_reference' in data:
  yy=[F(x) for x in data['simplex_reference']]
 else:
  import math
  widths=[data['theta'][i+1]-data['theta'][i] for i in range(8)]+[2*math.pi-data['theta'][8]]
  lf=.7389007860115458;df=9*lf-2*math.pi
  yr=[max(0,round((lf-v)/df*10**9)) for v in widths]
  if sum(yr)==0:yr=[1]*9
  yy=[F(x,sum(yr)) for x in yr]
 assert len(yy)==9 and all(x>=0 for x in yy) and sum(yy)==1
 theta=[i*L-D*sum(yy[:i]) for i in range(9)]
 energy=I(0);grad=[I(0) for _ in range(9)]
 for (i,j),qq in q.items():
  ang=theta[i]-theta[j];energy+=2*qq*(1-trig(ang,'cos'))
  z=2*qq*trig(ang,'sin');grad[i]+=z;grad[j]-=z
 # Linear term minimized on the simplex vertices.
 lin=[]
 for k in range(9):
  dev=[D*(sum(yy[:i])-F(int(k<i))) for i in range(9)]
  lin.append(sum((g*d for g,d in zip(grad,dev)),I(0)))
 linear=I(min(x.lo for x in lin),min(x.hi for x in lin))
 # Squared distance is convex; maximum on simplex occurs at a vertex.
 norm2=[]
 for k in range(9):
  norm2.append(D*D*sum((sum(yy[:i])-F(int(k<i)))**2 for i in range(9)))
 maxnorm=I(max(x.lo for x in norm2),max(x.hi for x in norm2))
 lower=energy+linear-I(kappa)*maxnorm/2
 assert lower.lo>U*U,('no exclusion',lower.dump(),str(U*U),'energy',energy.dump(),'linear',linear.dump(),'norm',maxnorm.dump())
 return {'status':'certified','proposition':'every anchor in full9-gap simplex and every free placement of specified witnessed triangulated-disk network has max edge length>U','blocks':blocks,'faces':faces,'edges':edges,'rational_weights':[str(x) for x in alpha],'simplex_reference':[str(x) for x in yy],'kappa':str(kappa),'constant_intervals':{'pi':pi.dump(),'L':L.dump(),'D':D.dump()},'dirichlet_pivots':piv,'curvature_pivots':mp,'energy_at_reference':energy.dump(),'linear_min':linear.dump(),'max_norm2':maxnorm.dump(),'lower_energy':lower.dump(),'U_squared':str(U*U),'margin_lower':str(lower.lo-U*U)}
if __name__=='__main__':
 name=sys.argv[1] if len(sys.argv)>1 else '234'
 kappa=F(sys.argv[2]) if len(sys.argv)>2 else F(3,1000)
 data=json.loads((P/'evidence'/('network-minimax-'+name+'.json')).read_text())
 out=verify(data,kappa)
 (P/'evidence'/('network-certified-'+name+'.json')).write_text(json.dumps(out,indent=2))
 print(json.dumps({'status':out['status'],'blocks':out['blocks'],'margin_lower_float_display':float(F(out['margin_lower'])),'dirichlet_pivots':len(out['dirichlet_pivots']),'curvature_pivots':len(out['curvature_pivots'])}))
