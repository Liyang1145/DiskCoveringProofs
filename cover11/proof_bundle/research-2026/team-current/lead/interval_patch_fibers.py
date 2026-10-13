"""C849 directed scalarfiber envelopes on OUTER INTERVALBOXES, not justpoints."""
import interval_joint_patch as k
from interval_joint_patch import iv,I,pi,R,z,asin,acos,lf,uf,pos,clip,sector,quad_range
import math,heapq,time,json

def setup(outer):
 r,b1,b2,A=outer;B=clip(b1+b2-A,0,pi)
 if B is None:return None
 s=iv.sqrt(1-r*r);bc=acos(r);eta=k.g/2;bmin=(bc+asin(iv.sin(eta)/r)-eta)/2
 if any(b.b<bmin.a or b.a>bc.b for b in [b1,b2]):return None
 widths=[]
 for b in [b1,b2]:
  X=-r*iv.cos(2*b+asin(r));D=s*s-2*s*r*iv.sin(b)*iv.cos(b)+2*r*r*iv.sin(b)**2
  if X.b<0:return None
  W=2*iv.atan2(pos(X),D);hi=min(W.b,(2*asin(r)).b)
  if hi<k.g.a:return None
  widths.append((lf(k.g),uf(I(hi))))
 de=b1-A;cs=iv.cos(de);disc=s*s*cs*cs-2*r*(1-r)
 if disc.b<0:return None
 root=iv.sqrt(pos(disc));hl=max((2*r*abs(iv.sin(de))).a,(s*cs-root).a,I(0).a);hh=min((2*r*iv.sin(b1+A)).b,(2*r*iv.sin(b2+B)).b,(s*cs+root).b,(2*r).b)
 if hh<hl:return None
 def widthbound(w,b,ii):
  raw=sector(r,s,b,w,ii)
  if raw is None:return None
  cb=iv.cos(b);sb=iv.sin(b);cx=s-2*r*sb*cb;cy=-2*r*sb*sb
  px=s*iv.cos(w)-r*iv.sin(w);py=-s*iv.sin(w)-r*iv.cos(w)
  dd=(px-cx)**2+(py-cy)**2
  orient=(px-cx)*(-r-cy)-(py-cy)*(s-cx)
  chordx=s-px;chordy=-r-py;lc=chordx*(cy-py)-chordy*(cx-px)
  # Meanvalue requiresunfilteredanalyticcontinuation for ALLouterpoints alongsegment.
  # Onlyapply whenno naturalenclosure clips areactive anywhereinbox.
  if dd.a<((R*I(19)/100)**2).b or dd.b>(r*r).a or orient.a<=0 or lc.a<=0:return raw
  cp=cx*px+cy*py;xx=cx*py-cy*px;u=iv.sqrt(dd)/R
  mu,h,d,dl=(z[1],z[112],z[34],z[96])if ii==1 else(z[3],z[115],z[39],z[101])
  grad=(1-cp)*(I(1)/2+(-mu-h)/dd)+h+(2*d+dl/u)*xx/(R*R)
  mid=I((float(w.a)+float(w.b))/2);center=sector(r,s,b,mid,ii)
  if center is None:return raw
  mean=center+grad*(w-mid)
  return I(max(raw.a,mean.a),min(raw.b,mean.b))
 def hf(H):
  ans=I(0)
  for b,th,az,bz,gz in [(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]:
   dd=2*r*iv.sin(b);yy=pos(dd*iv.sin(th));xx=H-dd*iv.cos(th);lsq=clip(xx*xx+yy*yy,I(1)/50000**2,4*r*r)
   if lsq is None:return None
   ee=iv.sqrt(lsq)/(2*R);ans+=H*yy/2+az*iv.atan2(yy,xx)+quad_range(bz,gz,ee)
  return ans
 w2=2*asin(r);K=pi*(z[113]+z[114]-z[2])+z[1]*(b1-pi+A)+z[3]*(b2-pi+B)+(w2-iv.sin(w2))/2+r*r*(iv.sin(2*b1)+iv.sin(2*b2))/2
 return K,[(lambda w:widthbound(w,b1,1),widths[0]),(lambda w:widthbound(w,b2,3),widths[1]),(hf,(lf(I(hl)),uf(I(hh))))]

def envelope(fun,dom,tol=1e-5,maxeval=10000):
 heap=[];uid=0;count=0;lower=-math.inf;terminal=-math.inf
 def add(l,h):
  nonlocal count,lower,terminal,uid
  v=fun(I(l,h));count+=1
  if v is None:return
  # floorforrelaxedintervalfunction: lf(pointenclosure) <= thatpoint's upper,
  # usableonly as SEARCHTHRESHOLD. Terminaluppersretained, so nofeasibilityclaim.
  p=fun(I((l+h)/2))
  if p is not None:lower=max(lower,uf(p)) # heuristicthresholdonly; allterminaluppersretained
  up=uf(v)
  if up<=lower:terminal=max(terminal,up)
  else:heapq.heappush(heap,(-up,uid,l,h));uid+=1
 add(*dom)
 while heap and -heap[0][0]>lower+tol and count<maxeval:
  neg,_,l,h=heapq.heappop(heap)
  if -neg<=lower:terminal=max(terminal,-neg);continue
  m=(l+h)/2
  if m==l or m==h:terminal=max(terminal,-neg);continue
  add(l,m);add(m,h)
 return {'upper':max(terminal,-heap[0][0] if heap else -math.inf),'search_floor':lower,'evaluations':count,'budget_ended':count>=maxeval}

def bound(outer,tol=1e-5,maxeval=10000):
 st=setup(outer)
 if st is None:return None
 K,fs=st;rr=[envelope(fun,dom,tol,maxeval)for fun,dom in fs]
 if any(row['upper']==-math.inf for row in rr):return None
 total=K+sum(I(row['upper'])for row in rr)
 return {'upper':uf(total),'constant':[lf(K),uf(K)],'fibers':rr}
if __name__=='__main__':
 from pathlib import Path
 P=k.P
 source=json.loads((P/'nested_patch_frozen_attack.json').read_text());rr=max(source['runs'],key=lambda a:a['value']);r,b1,b2,_,_,qa,_=rr['chart'];A=qa*(b1+b2)
 # decimals define exact local point; radius enlarged [.375,.38] scope.
 out=[]
 for eps in [0,1e-7]:
  outer=[I(str(v)) if eps==0 else I(v-eps,v+eps)for v in [r,b1,b2,A]];t=time.time();row=bound(outer,2e-6,20000);row.update(outer=[[lf(v),uf(v)]for v in outer],epsilon=eps,seconds=time.time()-t);out.append(row);print(row,flush=True)
 (P/'patch_fiber_mean_certificate.json').write_text(json.dumps({'scope':'two explicitouterboxes only, not globalpatchupper','rows':out},indent=2))
