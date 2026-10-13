"""Independent Fraction replay of concaveflow certificate; rebuildincidence via earlierFractionvalidator."""
from anchor_simplex_q10_fraction_replay import *
src=P/'anchor-concave-certificate.json';rec=json.loads(src.read_text());control=replay_record(rec);assert control['incidence_rebuilt']and control['exact_balance'];flow=rec['flow'];z=[list(map(F,p))for p in flow['flow_vectors']];q=10;nf=len(flow['faces']);g=[[-sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(q)];t0=list(map(F,flow['angle_center_radians']));delta=sub(mul(point(F(10)),L),mul(point(F(2)),pi));assert delta[1]<pi[0];den=sum((normup(p)for p in z),F(0))
def at(t,gg):
 mid=(t[0]+t[1])/2;err=(t[1]-t[0])/2;assert abs(mid)<4
 sn0=sum(((-1)**k*mid**(2*k+1)/math.factorial(2*k+1)for k in range(35)),F(0));cs0=sum(((-1)**k*mid**(2*k)/math.factorial(2*k)for k in range(36)),F(0));rem=abs(mid)**71/math.factorial(71);sn=rnd((sn0-rem,sn0+rem));cs=rnd((cs0-rem,cs0+rem))
 sn=(sn[0]-err,sn[1]+err);cs=(cs[0]-err,cs[1]+err);return add(mul(point(gg[0]),cs),mul(point(gg[1]),sn))
eta=[]
for j,gg in enumerate(g):
 hi=mul(point(F(j)),L);lo=sub(hi,delta if j else point(F(0)))
 if t0[j]<0:hi=sub(hi,mul(point(F(2)),pi));lo=sub(lo,mul(point(F(2)),pi))
 pos=at(lo,gg)[0]>=0 and at(hi,gg)[0]>=0;eta.append(F(0)if pos else normup(gg))
bounds=[]
for v in range(q):
 val=point(F(0))
 for j,gg in enumerate(g):
  t=sub(mul(point(F(j)),L),delta if v<j else point(F(0)))
  if t0[j]<0:t=sub(t,mul(point(F(2)),pi))
  dt=sub(t,point(t0[j]));val=add(val,sub(at(t,gg),mul(point(eta[j]/2),mul(dt,dt))))
 bounds.append(val[0]/den)
lo=min(bounds);lo=F(lo.numerator*S//lo.denominator,S);assert lo>U;out={'status':'independent_fraction_global_concave_flow_bound','family':'10/4','index':843,'lower_radius_exact':str(lo),'lower_radius_display':float(lo),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'endpoint_signs_all_positive':all(x==0 for x in eta),'incidence_rebuilt':True,'balance_exact':True};(P/'anchor-concave-fraction-replay.json').write_text(json.dumps(out,indent=2));print(out)
