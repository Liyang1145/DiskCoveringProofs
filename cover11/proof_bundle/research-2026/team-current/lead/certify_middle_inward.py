"""Continuous interval bound for conditionalsector2 with C844filter. No sample certification.
Run optional factorstart factorend, endexclusive. Frozen9decimalcoefficients. Boundedwork returns soundupper evenif nottightenough.
"""
from pathlib import Path
import sys,json,math,heapq,time,hashlib
P=Path(__file__).parent;lo=int(sys.argv[1]) if len(sys.argv)>1 else 0;hi=int(sys.argv[2]) if len(sys.argv)>2 else 29
frozen=P/'middle_inward_frozen.json';digest=hashlib.sha256(frozen.read_bytes()).hexdigest()
sys.argv=['x','0','4'];src=(P/'certify_q0_closure.py').read_text();assert src.count('# Heap entries')==1;src=src.split('# Heap entries')[0].replace("f'q0_closure_dual_{start}_{span}.json'","'middle_inward_frozen.json'")
ns={'__file__':str(P/'certify_q0_closure.py')};exec(src,ns)
iv=ns['iv'];iv.dps=30;z=ns['z'];pi=iv.pi;R=ns['R'];I=ns['interval'];uf=ns['upperfloat'];lf=ns['lowerfloat'];factors=ns['factors'];tmin=iv.mpf(75)/76
# filter only removes fullboxes rigorously infeasible; rawobjective still enclosesfullbox.
for fi in range(20,29):
 name,raw,dom=factors[fi]
 def filtered(box,raw=raw):
  a,u,v=box;q=(u-v)**2+4*u*v*iv.sin(a/2)**2;q=I(max(iv.mpf(0).a,q.a),min(iv.mpf(4).b,q.b));h=R*iv.sqrt(q)/2;k=iv.sqrt(1-h*h)
  lhs=u*v*(k*iv.sin(a)-h*iv.cos(a));m=I(max((tmin*tmin).a,(u*u).a,(v*v).a),max((tmin*tmin).b,(u*u).b,(v*v).b))
  if lhs.b<(m*h).a:return None
  return raw(box)
 factors[fi]=(name,filtered,dom)
def corner(box):
 t=box[0];w=2*ns['asin'](R*t);i=2
 return (w-iv.sin(w))/2-z[i]*pi-(z[32+2*i]+z[33+2*i])*t*t-(z[94+2*i]+z[95+2*i])*t+(z[71]+(z[113]+z[114])/2)*w
factors[22]=('ring2corner',corner,[(lf(tmin),1)])
for fi in range(lo,hi):
 name,fun,dom=factors[fi];outpath=P/f'middle_inward_bound_{fi:02d}.json'
 if outpath.exists():
  old=json.loads(outpath.read_text());assert old['coefficient_sha256']==digest;continue
 tol=.000005 if fi<20 or fi==22 else .000015
 heap=[];uid=0;count=0;lower=-1e100;discarded=-1e100;t0=time.time()
 def add(box):
  global uid,count,lower,discarded
  val=fun([I(l,h) for l,h in box]);count+=1
  if val is None:return
  pt=fun([iv.mpf((l+h)/2) for l,h in box])
  if pt is not None:lower=max(lower,lf(pt))
  upper=uf(val)
  if upper>=lower:heapq.heappush(heap,(-upper,uid,box));uid+=1
  else:discarded=max(discarded,upper)
 add(dom)
 while heap and -heap[0][0]>lower+tol and count<200000:
  neg,_,box=heapq.heappop(heap)
  if -neg<lower:discarded=max(discarded,-neg);continue
  kk=max(range(len(box)),key=lambda k:(box[k][1]-box[k][0])/(dom[k][1]-dom[k][0]));l,h=box[kk];m=(l+h)/2
  for pair in [(l,m),(m,h)]:new=box.copy();new[kk]=pair;add(new)
  if count%20000<3:print('PROGRESS',fi,count,-heap[0][0] if heap else None,lower,flush=True)
 upper=max(discarded,-heap[0][0] if heap else discarded);assert math.isfinite(upper)
 row={'factor_index':fi,'factor':name,'upper':upper,'lower_probe':lower,'evaluations':count,'seconds':time.time()-t0,'coefficient_sha256':digest,'tolerance':tol,'budget_ended':count>=200000}
 outpath.write_text(json.dumps(row,indent=2));print('BOUND',row,flush=True)
