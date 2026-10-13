"""Independent high-precision scalar formula vs interval box kernel. Calibration, not certification."""
from pathlib import Path
import sys,json,random,math
import mpmath as mp
P=Path(__file__).parent;mp.mp.dps=65
reports=[]
for script,stem,span,Rstr in [('certify_q0_closure.py','q0_closure_dual',3,'0.38'),('certify_q0_lower375.py','q0_lower375_dual',4,'0.375')]:
 sys.argv=[script,'0',str(span)];ns={'__file__':str(P/script)};exec((P/script).read_text(encoding='utf-8-sig').split('# Heap entries')[0],ns)
 J=json.loads((P/f'{stem}_0_{span}.json').read_text());z=[mp.mpf(f'{v:.9f}') for v in J['z']];R=mp.mpf(Rstr);fs=J['faces'];es=[tuple(e) for e in J['edges']];pi=mp.pi
 def Q(A,B):
  vals=[mp.mpf(0),A+B]
  if A<0 and 0<=-B/(2*A)<=1:vals.append(-B*B/(4*A))
  return max(vals)
 def scalar(tag,x):
  if tag.startswith('face'):
   t=int(tag[4:]);a,b=x;c=pi-a-b
   if c<0:return None
   aa=[a,b,c];s=list(map(mp.sin,aa));base=A=B=mp.mpf(0);A=2*R**2*s[0]*s[1]*s[2]
   for k,i in enumerate(fs[t]):
    e=tuple(sorted(j for j in fs[t] if j!=i));ei=es.index(e);adj=[tt for tt,f in enumerate(fs) if set(e)<=set(f)];sg=1 if adj[0]==t else -1
    base-= (z[i]+z[50+ei])*aa[k];A+=sg*z[11+ei]*s[k]**2;B+=sg*z[73+ei]*s[k]
   return base+Q(A,B)
  if tag.startswith('switch'):
   i=int(tag[6:]);j=(i+1)%9;ei=es.index(tuple(sorted((i,j))));b=x[0]
   A=R**2*mp.sin(2*b)/2-z[11+ei]*mp.sin(b)**2+z[32+2*i+1]+z[32+2*j];B=-z[73+ei]*mp.sin(b)+z[94+2*i+1]+z[94+2*j]
   return (z[i]+z[j]-z[50+ei]+2*z[112+i])*b+Q(A,B)
  i=int(tag[4:]);a,u,v=x;q=(u-v)**2+4*u*v*mp.sin(a/2)**2
  if q<4*mp.sin(pi-8*mp.asin(R))**2/R**2:return None
  w=2*mp.asin(R*mp.sqrt(q)/2);L=mp.atan2(v*mp.sin(a),u-v*mp.cos(a));T=pi-a-L
  return R**2*u*v*mp.sin(a)/2+(w-mp.sin(w))/2+z[71]*w-z[i]*a-z[32+2*i]*u*u-z[32+2*i+1]*v*v-z[94+2*i]*u-z[94+2*i+1]*v+z[112+(i-1)%9]*L+z[112+i]*T+(z[112+(i-1)%9]+z[112+i])*w/2
 rng=random.Random(820);checked=0;boxes=0
 for tag,fun,dom in ns['factors']:
  for trial in range(75):
   box=[]
   for l,h in dom:
    c=rng.uniform(l,h);rad=(h-l)*10**rng.uniform(-5,-.05);box.append((max(l,c-rad),min(h,c+rad)))
   val=fun([ns['interval'](l,h) for l,h in box]);boxes+=1
   for j in range(4):
    xx=[mp.mpf(rng.uniform(l,h)) for l,h in box];v=scalar(tag,xx)
    if v is None:continue
    assert val is not None,(tag,'discarded legal point')
    lo=mp.mpf(val.a._mpi_[0]);hi=mp.mpf(val.b._mpi_[1]);assert lo-mp.mpf('1e-22')<=v<=hi+mp.mpf('1e-22'),(tag,str(v),str(val),box)
    checked+=1
 reports.append({'script':script,'boxes':boxes,'scalar_points':checked,'enclosure_violations':0})
(P/'closure_box_control.json').write_text(json.dumps(reports,indent=2));print(reports)
