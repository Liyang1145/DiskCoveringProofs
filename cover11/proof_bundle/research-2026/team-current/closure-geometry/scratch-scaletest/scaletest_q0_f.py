"""Directed interval branch-and-bound for a proposed factor dual. Global boxes, not optimization certification.
Run with start span. Uses analytic face/switch squared-radius endpoint elimination.
"""
from mpmath import iv
import math,json,heapq,sys,time
from pathlib import Path
iv.dps=25;P=Path(__file__).parent;start=int(sys.argv[1]);span=int(sys.argv[2]);row=json.loads((P/f'q0_moment_dual_{start}_{span}.json').read_text())
z=[iv.mpf(f'{v:.9f}') for v in row['z']];R=iv.mpf(19)/50*iv.mpf(0.05);R2=R*R;pi=iv.pi;faces=row['faces'];edges=[tuple(e) for e in row['edges']];ne=len(edges);nf=len(faces);side=11;rr=32;kap=50;lam=71;eta=72;lin=73
assert ne==21 and nf==11 and all(v.a>=0 for v in z[kap:lin])
# independent graph assertion
expected=[(9,k,k+1) for k in range(span)]+[(10,k,(k+1)%9) for k in range(span,9)]+[(9,10,0),(9,10,span)]
assert z[eta]==0
assert sorted(tuple(sorted(f)) for f in faces)==sorted(tuple(sorted(f)) for f in expected)
assert edges==sorted({tuple(sorted((f[k],f[(k+1)%3]))) for f in expected for k in range(3)})
adj={e:[(t,next(k for k in f if k not in e)) for t,f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
def pos(x):return iv.mpf([max(iv.mpf(0).a,x.a),max(iv.mpf(0).b,x.b)])
def asin(x):return iv.atan2(x,iv.sqrt(1-x*x))
def interval(l,h):return iv.mpf([l,h])
def upperfloat(x):return math.nextafter(float(x.b),math.inf)
def lowerfloat(x):return math.nextafter(float(x.a),-math.inf)
def scalar_quad(a,b):
 a=iv.mpf(a);b=iv.mpf(b);zero=iv.mpf(0)
 if a.a>=0:return interval(max(zero.a,(a+b).a),max(zero.b,(a+b).b))
 if b.b<=0:return zero
 if (2*a+b).a>=0:return a+b
 peak=-b*b/(4*a)
 low=max(zero.a,(a+b).a)
 if (2*a+b).b<=0:low=max(low,peak.a)
 return interval(low,max(zero.b,(a+b).b,peak.b))
def quad(A,B):
 lo=scalar_quad(A.a,B.a);hi=scalar_quad(A.b,B.b)
 return interval(lo.a,hi.b)
# interval polynomial/trigonometric function values; naive interval gives a safe fallback
factors=[]
for t,f in enumerate(faces):
 co=[];dd=[];ll=[]
 for k,i in enumerate(f):
  e=tuple(sorted(j for j in f if j!=i));ee=edges.index(e);co.append(-z[i]-z[kap+ee]);dd.append(z[side+ee]*(1 if adj[e][0][0]==t else -1));ll.append(z[lin+ee]*(1 if adj[e][0][0]==t else -1))
 def fun(box,co=co,dd=dd,ll=ll):
  a,b=box;c=pi-a-b
  if c.b<0:return None
  c=interval(max(c.a,iv.mpf(0).a),min(c.b,pi.b));ang=[a,b,c]
  sn=[iv.sin(v) for v in ang];base=sum(co[k]*ang[k] for k in range(3));v=2*R2*sn[0]*sn[1]*sn[2]+sum(dd[k]*sn[k]**2 for k in range(3))
  linval=sum(ll[k]*sn[k] for k in range(3));direct=base+quad(v,linval)
  if a.a<0 or b.a<0 or (pi-a-b).a<0:return direct
  def arg_at(A,B):
   A=iv.mpf(A);B=iv.mpf(B);end=A+B
   if A.b<0:
    if B.b<=0:return iv.mpf(0)
    if (2*A+B).a>=0:return iv.mpf(1)
    if (2*A+B).b<=0 and B.a>=0:return -B/(2*A)
   elif A.a>=0:
    if end.a>0:return iv.mpf(1)
    if end.b<0:return iv.mpf(0)
   return interval(0,1)
  lowarg=arg_at(v.a,linval.a);hiarg=arg_at(v.b,linval.b)
  radius=interval(max(iv.mpf(0).a,lowarg.a),min(iv.mpf(1).b,hiarg.b))
  cs=[iv.cos(t) for t in ang]
  vv=[2*R2*cs[k]*sn[(k+1)%3]*sn[(k+2)%3]+2*dd[k]*sn[k]*cs[k] for k in range(3)]
  llgrad=[ll[k]*cs[k] for k in range(3)]
  grad=[co[k]-co[2]+radius**2*(vv[k]-vv[2])+radius*(llgrad[k]-llgrad[2]) for k in [0,1]]
  am=iv.mpf((float(a.a)+float(a.b))/2);bm=iv.mpf((float(b.a)+float(b.b))/2);cm=pi-am-bm
  ss=[iv.sin(t) for t in [am,bm,cm]];valm=2*R2*ss[0]*ss[1]*ss[2]+sum(dd[k]*ss[k]**2 for k in range(3));lm=sum(ll[k]*ss[k] for k in range(3))
  center=co[0]*am+co[1]*bm+co[2]*cm+quad(valm,lm)
  mean=center+grad[0]*(a-am)+grad[1]*(b-bm)
  return interval(max(direct.a,mean.a),min(direct.b,mean.b))
 factors.append(('face'+str(t),fun,[(0,upperfloat(pi)),(0,upperfloat(pi))]))
for bi in range(9):
 i,j=bi,(bi+1)%9;ee=edges.index(tuple(sorted((i,j))));c=z[i]+z[j]-z[kap+ee];d=z[side+ee];e=z[rr+2*i+1]+z[rr+2*j]
 g=-z[lin+ee];h=z[lin+21+2*i+1]+z[lin+21+2*j]
 def fun(box,c=c,d=d,e=e,g=g,h=h):
  b=box[0];v=R2*iv.sin(2*b)/2-d*iv.sin(b)**2+e
  # enlarge capped admissible x to [0,1], valid global relaxation (often identical optimum)
  return c*b+quad(v,g*iv.sin(b)+h)
 factors.append(('switch'+str(bi),fun,[(0,upperfloat(pi/2))]))
for i in range(9):
 mu=z[i];d=z[rr+2*i];e=z[rr+2*i+1];C=z[lam]+(z[eta] if i>=3 else 0)
 dl=z[lin+21+2*i];el=z[lin+21+2*i+1]
 def fun(box,mu=mu,d=d,e=e,C=C,dl=dl,el=el):
  a,u,v=box
  # q=(u-v)^2+4uv sin²(a/2) avoids interval cancellation
  q=(u-v)**2+4*u*v*iv.sin(a/2)**2;q=interval(max(iv.mpf(0).a,q.a),min(iv.mpf(4).b,q.b));w=2*asin(R*iv.sqrt(q)/2)
  wl=iv.mpf(w.a);wh=iv.mpf(w.b)
  h=interval(((C+iv.mpf('.5'))*wl-iv.sin(wl)/2).a,((C+iv.mpf('.5'))*wh-iv.sin(wh)/2).b)
  direct=R2*u*v*iv.sin(a)/2+h-mu*a-d*u*u-e*v*v-dl*u-el*v
  L=R/iv.sqrt(1-R2);den=iv.sqrt(1-R2*q/4)
  if q.a>0:
   root=iv.sqrt(q);wa=R*u*v*iv.sin(a)/(root*den);wu=R*(u-v*iv.cos(a))/(root*den);wv=R*(v-u*iv.cos(a))/(root*den)
   wa=interval(max(-L.b,wa.a),min(L.b,wa.b));wu=interval(max(-L.b,wu.a),min(L.b,wu.b));wv=interval(max(-L.b,wv.a),min(L.b,wv.b))
  else:wa=interval(-L.b,L.b);wu=interval(-L.b,L.b);wv=interval(-L.b,L.b)
  H=C+(1-iv.cos(w))/2
  grad=[R2*u*v*iv.cos(a)/2+H*wa-mu,R2*v*iv.sin(a)/2+H*wu-2*d*u-dl,R2*u*iv.sin(a)/2+H*wv-2*e*v-el]
  mids=[iv.mpf((float(t.a)+float(t.b))/2) for t in box];am,um,vm=mids;qm=(um-vm)**2+4*um*vm*iv.sin(am/2)**2;wm=2*asin(R*iv.sqrt(qm)/2)
  center=R2*um*vm*iv.sin(am)/2+(wm-iv.sin(wm))/2+C*wm-mu*am-d*um*um-e*vm*vm-dl*um-el*vm
  mean=center+sum(grad[k]*(box[k]-mids[k]) for k in range(3))
  return interval(max(direct.a,mean.a),min(direct.b,mean.b))
 factors.append(('ring'+str(i),fun,[(0,upperfloat(pi)),(0,1),(0,1)]))
# Heap entries with outward-safe float priorities; terminal bound taken from live queue.
result=[];total=pi*(sum(z[:9])+2*sum(z[9:11])+sum(z[kap:lam])-2*z[lam]-2*z[eta])+2*z[eta]*asin(2*R)
for name,fun,domain in factors:
 uid=0;heap=[];lower=-1e100;discarded_upper=-1e100;count=0;t0=time.time();tol=.001
 def add(box):
  global uid,lower,count,discarded_upper
  val=fun([interval(l,h) for l,h in box]);count+=1
  if val is None:return
  mids=[(l+h)/2 for l,h in box];point=fun([iv.mpf(m) for m in mids])
  if point is not None:lower=max(lower,lowerfloat(point))
  ub=upperfloat(val)
  if ub>=lower:heapq.heappush(heap,(-ub,uid,box));uid+=1
  else:discarded_upper=max(discarded_upper,ub)
 add(domain)
 while heap and -heap[0][0]>lower+tol:
  neg,_,box=heapq.heappop(heap)
  if -neg<lower:discarded_upper=max(discarded_upper,-neg);continue
  # scale widths by initial range; ring angle sensitivity comparable to radii
  k=max(range(len(box)),key=lambda k:(box[k][1]-box[k][0])/(domain[k][1]-domain[k][0]));l,h=box[k];m=(l+h)/2
  for pair in [(l,m),(m,h)]:new=box.copy();new[k]=pair;add(new)
  if count>1200000:raise RuntimeError(f'bounded certificate budget exceeded {name}: lower={lower} upper={-heap[0][0]}')
 ub=max(discarded_upper,-heap[0][0] if heap else discarded_upper);assert math.isfinite(ub);total+=iv.mpf(ub)
 result.append({'factor':name,'upper':ub,'lower':lower,'evaluations':count,'seconds':time.time()-t0});print(name,ub,count,round(time.time()-t0,2),flush=True)
 (P/f'SCALETEST_f_{start}_{span}.partial.json').write_text(json.dumps(result,indent=2))
assert total.b<pi.a,total
res={'start':start,'span':span,'upper':str(total),'pi':str(pi),'strict':True,'coefficients':[f'{v:.9f}' for v in row['z']],'factors':result}
(P/f'SCALETEST_f_{start}_{span}.json').write_text(json.dumps(res,indent=2));print('CERTIFIED',str(total),flush=True)

