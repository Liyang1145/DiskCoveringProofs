"""Independent directed-dyadic evaluation of mean-gauge Fraction controls.
Geometry formula theta_j=jL +sum_i((9-i)/10 -1_{i<j})d_i is direct,
not accumulatedprefix code. Shared existing trig/interval kernels disclosed.
"""
from q11_chord_flow_certificate import I,Q,S,L,PI,iv,P,json,trig
from q10_mean_gauge_control import gauge_replay
import hashlib

def dyadic(rec):
 assert rec.get('gauge')=='mean_prefix'
 flow=rec['flow'];nf=len(flow['faces']);z=[list(map(Q,v))for v in flow['flow_vectors']];g=[[-sum(z[3*nf+2*j+h][k]for h in range(2))for k in range(2)]for j in range(10)];den=sum((I(sum(x*x for x in v)).sqrt()for v in z),I(0));t0=list(map(Q,flow['angle_center_radians']));TT=[]
 for V in rec['polytope']['vertices']:
  dd=[iv(tuple(map(Q,v)))for v in V];tt=[]
  for j in range(10):
   t=j*L+sum((I(Q(9-i,10)-int(i<j))*dd[i]for i in range(10)),I(0))
   if t0[j]<0:t-=2*PI
   tt.append(t)
  TT.append(tt)
 def at(t,gg):
  sn,cs=trig(t);return I(gg[0])*cs+I(gg[1])*sn
 eta=[]
 for j,gg in enumerate(g):
  lo=I(min(t[j].lo for t in TT),min(t[j].lo for t in TT),True);hi=I(max(t[j].hi for t in TT),max(t[j].hi for t in TT),True);assert hi.hi-lo.lo<PI.lo
  eta.append(I(0)if at(lo,gg).lo>=0 and at(hi,gg).lo>=0 else I(sum(x*x for x in gg)).sqrt())
 lower=min(((sum((at(tt[j],g[j])-eta[j]*(tt[j]-I(t0[j]))**2/2 for j in range(10)),I(0)))/den).lo for tt in TT)
 return Q(lower,S)

if __name__=='__main__':
 out=[]
 for name in ['q10-mean-gauge-control.json','q10-mean-gauge-near-threshold.json']:
  src=P/name;a=json.loads(src.read_text());c=a['certificate'];fr=gauge_replay(c);lo=dyadic(c);assert abs(lo-Q(fr['lower_exact']))<Q(1,10**35);assert (lo>Q('.33173203427623414'))==fr['excluded'];out.append(dict(source=name,sha256=hashlib.sha256(src.read_bytes()).hexdigest(),fraction=fr,dyadic_lower_exact=str(lo)));print('MEANGAUDIT',name,float(lo),fr['excluded'],flush=True)
 (P/'q10-mean-gauge-audit.json').write_text(json.dumps(dict(status='direct_affine_dyadic_replay_two_controls',scope='kernelcontrols only; treecoverage unchanged',runs=out),indent=2))
