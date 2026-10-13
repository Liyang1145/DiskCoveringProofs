"""Independent Fraction global-simplex dual replay: incidence rebuilt; no producer functions."""
from area_safe_fraction_replay import F,P,U,pi,L,add,neg,mul,div,point,trig
import json,math,hashlib
S=10**45
def rnd(iv):return(F(iv[0].numerator*S//iv[0].denominator,S),F(-((-iv[1].numerator*S)//iv[1].denominator),S))
pi=rnd(pi);L=rnd(L)
def normup(v):
 a=sum(x*x for x in v);k=math.isqrt(a.numerator*S*S//a.denominator);ans=F(k+1,S)if a else F(0);assert ans*ans>=a;return ans
def sub(a,b):return add(a,neg(b))
def replay_record(rec):
 flow=rec['flow'];faces=json.loads((P/'k10-catalogue-corrected.json').read_text())['10/4'][rec['index']]['faces'];assert faces==flow['faces'];q=10;nf=len(faces);nv=14+nf;owners=[[i,(i+1)%q]for i in range(q)];assert owners==flow['owners'];inc=[]
 for j,vs in enumerate(faces):
  for v in vs:
   d=[0]*nv;d[v]=1;d[14+j]=-1;inc.append(d)
 for vs in owners:
  for v in vs:
   d=[0]*nv;d[v]=1;inc.append(d)
 assert inc==flow['incidence_matrix'];z=[list(map(F,p))for p in flow['flow_vectors']];assert all(sum(inc[e][u]*z[e][k]for e in range(len(inc)))==0 for u in range(nv)for k in range(2))
 assert sub(mul(point(F(2)),pi),mul(point(F(9)),L))[0]>0;delta=sub(mul(point(F(10)),L),mul(point(F(2)),pi));assert delta[0]>0 and sub(L,delta)[0]>0
 den=sum((normup(v)for v in z),F(0));g=[[-sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(q)];t0=list(map(F,flow['angle_center_radians']));F0=point(F(0));grad=[]
 for t,gg in zip(t0,g):
  sn,cs=map(rnd,trig(abs(t)))
  if t<0:sn=neg(sn)
  F0=add(F0,add(mul(point(gg[0]),cs),mul(point(gg[1]),sn)));grad.append(add(mul(point(-gg[0]),sn),mul(point(gg[1]),cs)))
 bounds=[]
 for v in range(q):
  val=F0
  for j in range(q):
   t=sub(mul(point(F(j)),L),delta if v<j else point(F(0)))
   if t0[j]<0:t=sub(t,mul(point(F(2)),pi))
   dt=sub(t,point(t0[j]));val=add(val,sub(mul(grad[j],dt),mul(point(normup(g[j])/2),mul(dt,dt))))
  bounds.append(val[0]/den)
 lower=min(bounds);lowround=F(lower.numerator*S//lower.denominator,S);
 return {'family':'10/4','index':rec['index'],'lower_radius_exact':str(lowround),'lower_radius_display':float(lowround),'excluded':lowround>U,'incidence_rebuilt':True,'exact_balance':True,'vertices':10}
if __name__=='__main__':
 import time
 start=time.time();src=P/'anchor-simplex-q10-certificates.json';data=json.loads(src.read_text());out=[]
 for rec in data['runs']:
  if rec['status']!='excluded_pending_fraction_replay':continue
  row=replay_record(rec);assert row['excluded'];out.append(row);print(row['index'],row['lower_radius_display'],flush=True)
  (P/'anchor-simplex-q10-fraction-replay.json').write_text(json.dumps({'status':'independent_fraction_global_domain_replays','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'runs':out,'seconds':time.time()-start},indent=2))
 print('DONE',len(out),'seconds',time.time()-start,flush=True)
