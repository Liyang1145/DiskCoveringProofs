"""Conditional interval certificate for endpoint-sector degeneration; reuse audited C820kernel.
No original certificate or proposer output overwritten. Each factor<=600k eval budget.
"""
from pathlib import Path
import sys,json,math,heapq,time
P=Path(__file__).parent
sys.argv=['certify_q0_closure.py','0','4']
ns={'__file__':str(P/'certify_q0_closure.py')}
src=(P/'certify_q0_closure.py').read_text().replace("f'q0_closure_dual_{start}_{span}.json'","'endpoint_frozen_dual_0_4.json'");exec(src.split('# Heap entries')[0],ns)
iv=ns['iv'];iv.dps=25;z=ns['z'];pi=iv.pi;R=ns['R'];interval=ns['interval'];upperfloat=ns['upperfloat'];lowerfloat=ns['lowerfloat']
factors=ns['factors'];const=pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[50:71])-2*z[71])-pi*sum(z[112:])
# conditional corner at sectori: alpha=pi, u=v=1, forced by inwardnorm/chordgeometry.
w=2*ns['asin'](R)
def corner(i):return (w-iv.sin(w))/2-z[i]*pi-z[32+2*i]-z[33+2*i]-z[94+2*i]-z[95+2*i]+z[71]*w+(z[112+(i-1)%9]+z[112+i])*w/2
partial=P/'endpoint_sector_corner.partial.json'
out=json.loads(partial.read_text()) if partial.exists() else []
for name,fun,domain in factors:
 if any(row['factor']==name for row in out):continue
 uid=0;heap=[];lower=-1e100;discarded=-1e100;count=0;t0=time.time();tol=.0006
 def add(box):
  global uid,lower,count,discarded
  val=fun([interval(l,h) for l,h in box]);count+=1
  if val is None:return
  mid=[(l+h)/2 for l,h in box];point=fun([iv.mpf(m) for m in mid])
  if point is not None:lower=max(lower,lowerfloat(point))
  ub=upperfloat(val)
  if ub>=lower:heapq.heappush(heap,(-ub,uid,box));uid+=1
  else:discarded=max(discarded,ub)
 add(domain)
 while heap and -heap[0][0]>lower+tol:
  neg,_,box=heapq.heappop(heap)
  if -neg<lower:discarded=max(discarded,-neg);continue
  k=max(range(len(box)),key=lambda k:(box[k][1]-box[k][0])/(domain[k][1]-domain[k][0]));l,h=box[k];m=(l+h)/2
  for pair in [(l,m),(m,h)]:new=box.copy();new[k]=pair;add(new)
  if count%10000<3:print('PROGRESS',name,count,-heap[0][0],lower,flush=True)
  if count>600000:raise RuntimeError(f'factor budget {name}: ub={-heap[0][0]},lb={lower}')
 ub=max(discarded,-heap[0][0] if heap else discarded);assert math.isfinite(ub)
 out.append({'factor':name,'upper':ub,'lower':lower,'evals':count,'seconds':time.time()-t0});print(name,ub,count,round(time.time()-t0,2),flush=True)
 (P/'endpoint_sector_corner.partial.json').write_text(json.dumps(out,indent=2))
total=const+sum(iv.mpf(v['upper']) for v in out);rows=[]
for i in [0,4]:
 conditional=const+sum(iv.mpf(v['upper']) for v in out if v['factor']!='ring'+str(i))+corner(i)
 rows.append({'sector':i,'upper':str(conditional),'strict':bool(conditional.b<pi.a),'corner':str(corner(i))})
result={'scope':'continuous allfactor domain, conditionalalphaπ,u=v1 atsector0or4; not sharpoptimum','R':'19/50','coefficients':[str(x) for x in z],'full_relaxation_upper':str(total),'conditional':rows,'pi':str(pi),'factors':out}
(P/'endpoint_sector_corner_certificate.json').write_text(json.dumps(result,indent=2));print(rows,flush=True);assert all(r['strict'] for r in rows)
