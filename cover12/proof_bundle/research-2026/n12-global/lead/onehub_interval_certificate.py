"""Full k11 two-circle capacity certificate using mpmath.iv directed arithmetic.
Exact rational weights and domain parametrization. No float endpoints, no atan unwrap.
Saved scout weights are proposals only. Every scalar operation bearing on acceptance
is interval; floating scores only choose which exact rational box to split."""
from fractions import Fraction as F
from pathlib import Path
import json,time,sys,hashlib
from mpmath import iv
iv.dps=30
P=Path(__file__).resolve().parents[1]
Uq=F('0.361102963744508672616920293904')
def Q(x):
 x=F(x);return iv.mpf(x.numerator)/iv.mpf(x.denominator)
U=Q(Uq);E=3*U-1;rl=1-U;rh=iv.sqrt(1-U*U)
def box(a,b):return iv.mpf([Q(a).a,Q(b).b])
def clip01(x):return iv.mpf([max(x.a,iv.mpf(0)),min(x.b,iv.mpf(1))])
def acos01(x):
 x=clip01(x);return iv.atan2(iv.sqrt(clip01(1-x*x)),x)
def aggregate(rows):
 d={'boundary':[F(0)]*3,'hub':[F(0)]*3}
 for row in rows:
  name=row['row'];v=F(round(F(str(row['weight']))*10**9),10**9)
  assert v>=0
  circle=name.split('_')[0];d[circle][0]+=v
  if 'cos' in name:d[circle][1]+=v*int(name.split('_')[-1])
  if 'sin' in name:d[circle][2]+=v*int(name.split('_')[-1])
 assert all(a>=abs(b)+abs(c) for a,b,c in d.values())
 return d
def upper(d,B):
 z=box(*B[0]);ph=2*iv.pi*box(*B[1]);e=E*box(*B[2])
 rho=rl+(rh-rl)*z;co=iv.cos(ph);si=iv.sin(ph)
 qa=(1+rho*rho-U*U)/(2*rho);al=acos01(qa);sa=iv.sqrt(clip01(1-qa*qa))
 wb=[Q(v) for v in d['boundary']];wh=[Q(v) for v in d['hub']]
 val=wb[0]*al+sa*(wb[1]*co+wb[2]*si)
 dx=rho*co-e;dy=rho*si
 # use polar distance expression to avoid dependency zero lower bound at wide phi.
 ell2=rho*rho+e*e-2*rho*e*co
 if ell2.a<=0:return None
 ell=iv.sqrt(ell2)
 if ell.a>= (2*U).b:return val
 qb=ell/(2*U)
 # Entirely above1 already excluded. Clip cap branch to beta=0 beyond ell=2U.
 qb=iv.mpf([min(qb.a,iv.mpf(1)),min(qb.b,iv.mpf(1))])
 be=acos01(qb);sb=iv.sqrt(clip01(1-qb*qb))
 return val+wh[0]*be+sb*(wh[1]*dx/ell+wh[2]*dy/ell)
def verify_segment(d,lo,hi,maxboxes=100000,ring_count=11):
 assert ring_count in (10,11)
 target=iv.pi*Q(d['boundary'][0]+d['hub'][0])/ring_count
 stack=[((F(0),F(1)),(F(0),F(1)),(lo,hi))];n=leaves=0;worst=iv.mpf(0);maxdepth=0
 while stack:
  B=stack.pop();n+=1
  assert n<=maxboxes,('budget stop',n,len(stack))
  try:v=upper(d,B)
  except (ValueError,AssertionError):v=None
  if v is not None and v.b<target.a:
   leaves+=1
   if v.b>worst:worst=v.b
   continue
  widths=[float(b-a)*s for (a,b),s in zip(B,[1,6,0.3])];k=max(range(3),key=lambda k:widths[k])
  a,b=B[k];assert b-a>F(1,2**30),('unresolved tiny box',B)
  m=(a+b)/2
  for pair in [(a,m),(m,b)]:
   child=list(B);child[k]=pair;stack.append(tuple(child))
 def exact_endpoint(x,side):
  sign,man,exp,bc=x._mpi_[side]
  return str(F((-1 if sign else 1)*man)*(F(2)**exp))
 return {'boxes':n,'leaves':leaves,'upper':str(worst),'target':str(target),'upper_exact':exact_endpoint(worst,1),'target_lower_exact':exact_endpoint(target,0),'ring_count':ring_count,'weights':{k:[str(x) for x in v] for k,v in d.items()},'e_fraction':[str(lo),str(hi)]}
if __name__=='__main__':
 data=json.loads((P/'members/structure/onehub-dual/segment_U_K1.json').read_text())['segments'];N=len(data)
 indices=list(range(N)) if len(sys.argv)==1 else [int(sys.argv[1])]
 rows=[];start=time.time()
 for k in indices:
  d=aggregate(data[k]['weights']);row=verify_segment(d,F(k,N),F(k+1,N));rows.append(row)
  print(json.dumps({'segment':k,'boxes':row['boxes'],'upper':row['upper'],'target':row['target'],'seconds':time.time()-start}),flush=True)
  (P/'evidence'/('onehub-interval-'+('all' if len(indices)>1 else str(k))+'.json')).write_text(json.dumps({'status':'certified listed segments','exact_U':str(Uq),'kernel_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256((P/'members/structure/onehub-dual/segment_U_K1.json').read_bytes()).hexdigest(),'mpmath_iv_dps':iv.dps,'segments':rows},indent=2))
