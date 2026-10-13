"""Five savedboxes outer MVT with scalar subpartition; bounded methodtest."""
from pathlib import Path
import json,time
import interval_hub_saturated as raw
from saturated_outer_jet import parts,Unsafe
import interval_patch_delta as fibers
from interval_joint_patch import I,uf
P=Path(__file__).parent;rows=[];start=time.time()
for row in json.loads((P/'patch_outer_hub_boundary_certificate.json').read_text())['topboxes']:
 outer=[I(*q)for q in row['box']];mid=[I((float(x.a)+float(x.b))/2)for x in outer];K,ws,bs=raw.setup(outer);widthdoms=[dom for f,dom in ws];res=[]
 for j in [0,1]:
  try:
   Kj,fs=parts(outer,j);Km,fm=parts(mid,j);base=Km.v;grad=Kj.d[:3]
   for f,fc,(lo,hi)in zip(fs[:2],fm[:2],widthdoms):
    vals=[f(I(lo+(hi-lo)*k/16,hi if k==15 else lo+(hi-lo)*(k+1)/16))for k in range(16)]
    for k in range(3):grad[k]+=I(min(v.d[k].a for v in vals),max(v.d[k].b for v in vals))
    base+=I(fibers.envelope(lambda w:fc(w).v,(lo,hi),1e-5,65)['upper'])
   old,dom=bs[j];stats={'safe':0,'unsafe':0}
   wup=[fibers.envelope(fun,dom,1e-5,129)['upper']for fun,dom in ws]
   def fun(de):
    rawval=old(de)
    if rawval is None:return None
    val=K+sum((I(x)for x in wup),I(0))+rawval
    try:
     h=fs[2](de);hc=fm[2](de).v;der=[a+b for a,b in zip(grad,h.d[:3])]
     mv=base+hc+sum((d*(x-m)for d,x,m in zip(der,outer,mid)),I(0));stats['safe']+=1
     return I(min(val.a,mv.a),min(val.b,mv.b)) # lowerunused searchheuristic only
    except Unsafe:stats['unsafe']+=1;return val
   ans=fibers.envelope(fun,dom,1e-5,129);res.append({'upper':ans['upper'],'stats':stats})
  except Unsafe as e:res.append({'failure':str(e)})
 rows.append({'box':row['box'],'old':row['upper'],'faces':res})
out={'scope':'fiveboxcomparison notglobal','rows':rows,'seconds':time.time()-start};(P/'saturated_outer_mean_probe.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
