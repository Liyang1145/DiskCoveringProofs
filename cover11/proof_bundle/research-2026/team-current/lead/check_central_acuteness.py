"""Exact rational interval replay independent of alternative's mpmath arithmetic.
Uses inspected C904 Fraction primitives (not its decimal JSON outputs).
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util,json
P=Path(__file__).resolve().parent
src=P.parent/'r20-gluing/r23_central_screen_audit.py'
spec=importlib.util.spec_from_file_location('fraction_kernel',src);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
iv,add,sub,mul,scale,sqrt,dot,norm=m.iv,m.iadd,m.isub,m.imul,m.iscale,m.sqrt_iv,m.dot,m.norm
va,vs,vm,vmiv=m.vadd,m.vsub,m.vscale,m.vscale_iv
raw=json.loads((m.ROOT/'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C=[tuple(F(int(t),10**17) for t in row) for row in raw['centers_scaled_1e17']]
D=F(1,1000);W=F(1,10000);rI=iv(m.R_UB-W,m.R_UB+W);r2=mul(rI,rI)
rings=[tuple(iv(c-D,c+D) for c in C[i]) for i in m.NEW2RAW_RINGS]
pins={}
for i in range(9):
 a,b=rings[i],rings[(i+1)%9];u=vs(b,a);d2=dot(u,u);assert d2[0]>0
 d=sqrt(d2);rad=sub(r2,scale(d2,F(1,4)));assert rad[0]>0
 mid=vm(va(a,b),F(1,2));n=(m.idiv((-u[1][1],-u[1][0]),d),m.idiv(u[0],d));off=vmiv(n,sqrt(rad))
 p,q=va(mid,off),vs(mid,off);pn,qn=norm(p),norm(q)
 if pn[1]<qn[0]:pins[i]=p
 elif qn[1]<pn[0]:pins[i]=q
 else:raise AssertionError('undecided pin branch')
def hubbox(weights,fan):
 assert sum(w for w,i in weights)==1 and all(w>0 for w,i in weights)
 b=(iv(0),iv(0));V=iv(0)
 for w,i in weights:b=va(b,vm(pins[i],w))
 for j,(w,i) in enumerate(weights):
  for w2,i2 in weights[j+1:]:
   diff=vs(pins[i],pins[i2]);V=add(V,scale(dot(diff,diff),w*w2))
 rad=sub(r2,V);assert rad[1]>0
 eps=sqrt((max(rad[0],F(0)),rad[1]))
 boxes=[m.bbox_disk((iv(0),iv(0)),sub(iv(1),rI)),m.bbox_disk(b,eps)]+[m.bbox_disk(pins[i],rI) for i in fan]
 box=m.bbox_inter(boxes);assert all(x[0]<=x[1] for x in box)
 return box
A=hubbox(m.WL,m.FAN_A);B=hubbox(m.WB,m.FAN_B)
res={'ring_halfwidth':str(D),'radius_halfwidth':str(W),'r0':str(m.R_UB),'A':[[str(x) for x in t] for t in A],'B':[[str(x) for x in t] for t in B],'faces':{}}
for i in m.CENTRAL:
 c=rings[i]
 vals=[dot(vs(B,A),vs(c,A)),dot(vs(A,B),vs(c,B)),dot(vs(A,c),vs(B,c))]
 assert all(t[0]>F(1,50) for t in vals)
 res['faces'][str(i)]=[[str(x) for x in t] for t in vals]
 print('face',i,'vertex dot lower bounds',[float(t[0]) for t in vals])
res['all_six_dot_lower_bounds_gt_1_over_50']=True
Path(__file__).with_suffix('.json').write_text(json.dumps(res,indent=2),encoding='utf8')
