"""Independent Fraction arithmetic: incidence/sourcefaces/forces checked, symbolicvertex input separatelyaudited."""
from area_safe_fraction_replay import F,P,U,pi,L,add,neg,mul,point
import math,json,hashlib
from functools import lru_cache
S=10**45
def rnd(v):return(F(v[0].numerator*S//v[0].denominator,S),F(-((-v[1].numerator*S)//v[1].denominator),S))
pi=rnd(pi);L=rnd(L);x=2*U;N=100;bb=2*sum((F(math.comb(2*k,k),4**k*(2*k+1))*x**(2*k+1)for k in range(N)),F(0));B=rnd((bb,bb+2*x**(2*N+1)/(1-x*x)))
def sub(a,b):return add(a,neg(b))
def iv(v):return add(add(mul(point(v[0]),L),mul(point(v[1]),B)),mul(point(2*v[2]),pi))
def normup(v):
 a=sum(x*x for x in v);k=math.isqrt(a.numerator*S*S//a.denominator);return F(k+1,S)if a else F(0)
@lru_cache(None)
def sc(t):
 mid=(t[0]+t[1])/2;err=(t[1]-t[0])/2;assert abs(mid)<4;sn=sum(((-1)**k*mid**(2*k+1)/math.factorial(2*k+1)for k in range(35)),F(0));cs=sum(((-1)**k*mid**(2*k)/math.factorial(2*k)for k in range(36)),F(0));rem=abs(mid)**71/math.factorial(71);return rnd((sn-rem-err,sn+rem+err)),rnd((cs-rem-err,cs+rem+err))
def at(t,g):
 sn,cs=sc(t);return add(mul(point(g[0]),cs),mul(point(g[1]),sn))
def replay(rec):
 flow=rec['flow'];q=len(flow['owners']);source=json.loads((P/('q11-pocket-catalogue.json'if q==11 else'k10-catalogue-corrected.json')).read_text());faces=source['entries'if q==11 else'10/4'][rec['index']]['faces'];assert faces==flow['faces'];nf=len(faces);nv=14+nf;inc=[];owners=[[i,(i+1)%q]for i in range(q)];assert owners==flow['owners']
 for j,f in enumerate(faces):
  for v in f:
   d=[0]*nv;d[v]=1;d[14+j]=-1;inc.append(d)
 for vs in owners:
  for v in vs:
   d=[0]*nv;d[v]=1;inc.append(d)
 assert inc==flow['incidence_matrix'];z=[list(map(F,p))for p in flow['flow_vectors']];assert all(sum(inc[e][u]*z[e][k]for e in range(len(inc)))==0 for u in range(nv)for k in range(2));g=[[-sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(q)];den=sum((normup(p)for p in z),F(0));t0=list(map(F,flow['angle_center_radians']));TT=[]
 for V in rec['polytope']['vertices']:
  dd=[iv(tuple(map(F,v)))for v in V];ts=[]
  for j in range(q):
   t=mul(point(F(j)),L)
   for v in dd[:j]:t=sub(t,v)
   if t0[j]<0:t=sub(t,mul(point(F(2)),pi))
   ts.append(t)
  TT.append(ts)
 eta=[]
 for j,gg in enumerate(g):
  lo=min(t[j][0]for t in TT);hi=max(t[j][1]for t in TT);assert hi-lo<pi[0];positive=at(point(lo),gg)[0]>=0 and at(point(hi),gg)[0]>=0;eta.append(F(0)if positive else normup(gg))
 bounds=[]
 for tt in TT:
  val=point(F(0))
  for j,t in enumerate(tt):
   dt=sub(t,point(t0[j]));val=add(val,sub(at(t,g[j]),mul(point(eta[j]/2),mul(dt,dt))))
  bounds.append(val[0]/den)
 lo=min(bounds);lo=F(lo.numerator*S//lo.denominator,S);return {'family':'11/3'if q==11 else'10/4','index':rec['index'],'lower_radius_exact':str(lo),'lower_radius_display':float(lo),'excluded':lo>U,'vertices':len(TT),'incidence_rebuilt':True,'exact_balance':True,'vertex_coverage':'pending_separate_independent_audit','all_endpoint_signs_positive':all(x==0 for x in eta)}
if __name__=='__main__':
 src=P/'q11-chord-flow-control-certificates.json';out=[]
 for rec in json.loads(src.read_text())['runs']:
  if rec['status']=='excluded_pending_fraction_replay':
   r=replay(rec);out.append(r);print(r,flush=True)
 (P/'q11-chord-flow-fraction-replay.json').write_text(json.dumps({'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'runs':out},indent=2))
