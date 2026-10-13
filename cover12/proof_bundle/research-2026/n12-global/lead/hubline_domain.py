"""Adaptive full-domain cover by infeasible boxes or atomic dual boxes.
Budgeted runs persist queue and exact rational leaves, never label a partial
run globally certified. Domain s∈[1/20,U], x∈[0,1-U-1/20], y∈[0,e0].
Endpoint s=U can be excluded separately by separated-hub theorem.
"""
import hubline_atoms_fast as AF
import hubline_capacity as H
from fractions import Fraction as F
from pathlib import Path
from mpmath import iv
import json,sys,time,hashlib
U=H.K.Uq;a=1-2*U;e0=3*U-1
OUT=H.K.P/'evidence/hubline-domain.json'
def encode(B):return [[str(v) for v in r] for r in B]
def decode(B):return tuple(tuple(F(v) for v in r) for r in B)
def interval_square(l,h):return (F(0) if l<=0<=h else min(l*l,h*h),max(l*l,h*h))
def normlower(X,Y):return interval_square(*X)[0]+interval_square(*Y)[0]
CORE=[(a*c,a*s) for c,s in AF.A.units(32)]
def infeasible(B):
 (sl,sh),(xl,xh),(yl,yh)=B
 if normlower((xl+sl,xh+sh),(yl,yh))>(1-U)**2:return 'outer hub inactive'
 # Necessary point witnesses on core circle; exact rational.
 h1x=(xl-sh,xh-sl);h2x=(xl+sl,xh+sh)
 for cx,cy in CORE:
  d1=normlower((h1x[0]-cx,h1x[1]-cx),(yl-cy,yh-cy))
  d2=normlower((h2x[0]-cx,h2x[1]-cx),(yl-cy,yh-cy))
  if min(d1,d2)>U*U:return 'rational core witness'
 if xh<a:
  # sl²+(yl+sqrt(a²-xh²))²>U², exact radical-free comparison.
  q2=a*a-xh*xh;rhs=U*U-sl*sl-yl*yl-q2
  if rhs<0 or 4*yl*yl*q2>rhs*rhs:return 'core bisector endpoints'
 return None

def save_state(stack,leaves,counts):
 state={'status':'certified full domain' if not stack else 'partial','domain':[['1/20',str(U)],['0',str(1-U-F(1,20))],['0',str(e0)]],'counts':counts,'pending':[encode(B) for B in stack],'leaves':leaves,'hashes':{Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest() for m in [AF,AF.A,H]}}
 tmp=OUT.with_suffix('.tmp');tmp.write_text(json.dumps(state,indent=2));tmp.replace(OUT)
 return state

def run(budget=100):
 if OUT.exists():state=json.loads(OUT.read_text());stack=[decode(b) for b in state['pending']];leaves=state['leaves'];counts=state['counts']
 else:stack=[((F(1,20),U),(F(0),1-U-F(1,20)),(F(0),e0))];leaves=[];counts={'infeasible':0,'certified':0,'split':0,'processed':0}
 t=time.time()
 for it in range(budget):
  if not stack:break
  if it and it%100==0:save_state(stack,leaves,counts)
  B=stack.pop();counts['processed']+=1;why=infeasible(B)
  if why:counts['infeasible']+=1;leaves.append({'H':encode(B),'type':'infeasible','reason':why});continue
  widths=[b-a for a,b in B];maxw=max(widths)
  result=None;p=None
  # Large boxes first split: atom union bound useless when wider than circle margin.
  if maxw<=F(1,40):
   mid=[float((a+b)/2) for a,b in B];mid[0]=min(mid[0],float(U)-1e-15)
   p=H.propose(*mid,order=4,nr=24,np_=120)
   if p['numeric_max']<.099:
    C=AF.FastAtoms(B,p['weights'],2048);result=C.certify(budget=200000)
    if result['status']=='certified':
     counts['certified']+=1;leaves.append({'H':encode(B),'type':'atomic','proposal':p,'result':result});continue
  # Repair undersampled LP/atomic proposals before making tiny hub boxes.
  # Acceptance uses the independently audited pure-integer kernel, not the LP value.
  if maxw<=F(1,40) and result is not None and result['status']!='certified':
   sys.path.insert(0,str(H.K.P/'members/upper-audit/integer-atomic/py'))
   from integer_kernel_n import IntAtomsN
   vectors=str(H.K.P/'members/upper-audit/integer-atomic/evidence/canonical-unit-vectors-8192.json')
   dense=H.propose(*mid,order=6,nr=96,np_=720)
   dc=IntAtomsN(B,dense['weights'],vectors,Sexpt=26)
   dr=dc.certify(budget=400000)
   if dr['status']=='certified':
    counts['certified']+=1;leaves.append({'H':encode(B),'type':'atomic','atomN':8192,'proposal':dense,'result':dr,'kernel':'pure-int64-N'})
    continue
  k=max(range(3),key=lambda j:widths[j]);l,h=B[k];m=(l+h)/2
  if h-l<F(1,100000):
   counts['processed']-=1 # unresolved requeued box has not been processed into a leaf/split
   stack.append(B)
   print(json.dumps({'stuck':encode(B),'proposal':p,'result':result}),flush=True)
   break
  for v in [(l,m),(m,h)]:child=list(B);child[k]=v;stack.append(tuple(child))
  counts['split']+=1
  if counts['processed']%20==0:print(json.dumps({'counts':counts,'pending':len(stack),'seconds':time.time()-t,'last_width':float(maxw),'last_numeric':p and p['numeric_max']}),flush=True)
 state=save_state(stack,leaves,counts)
 print(json.dumps({'status':state['status'],'counts':counts,'pending':len(stack),'seconds':time.time()-t}),flush=True)
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 100)
