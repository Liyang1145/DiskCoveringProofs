from pathlib import Path
import json,random
import face_second_jet as f
import face_derivative_outer_jet as g
from interval_joint_patch import I,uf
P=Path(__file__).parent;rng=random.Random(869);rows=[]
for j in [0,1]:
 for k in range(15):
  p=[rng.uniform(.379,.37999),rng.uniform(1,1.18),rng.uniform(1,1.18),rng.uniform(-.4,.4)];x=[I(str(t))for t in p]
  a=f.objective(x,j);b=g.derivative(x,j)
  assert (a.d-b.v).a<=0<=(a.d-b.v).b and (a.h-b.d[3]).a<=0<=(a.h-b.d[3]).b
  errors=[]
  for i in range(4):
   h=I('1e-6');xp=x.copy();xm=x.copy();xp[i]+=h;xm[i]-=h;fd=(f.objective(xp,j).d-f.objective(xm,j).d)/(2*h);errors.append(uf(abs(fd-b.d[i])))
  rows.append({'j':j,'point':p,'fd_gradient_errors':errors})
saved=json.loads((P/'stationary_face_bound_probe.json').read_text())['topboxes'];boxes=[]
for row in saved:
 x=[I(l,h)for l,h in row['box']];j=row['j'];a=f.saturated(x,j);e,der=g.enclosure(x,j);boxes.append({'j':j,'box':row['box'],'natural':str(a.d),'outer_mvt':str(e),'excludes':bool(e.a>0 or e.b<0)})
out={'calibration':rows,'saved_boxes':boxes};(P/'face_derivative_outer_control.json').write_text(json.dumps(out,indent=2));print('30point analytic overlaps; max FD error',max(max(r['fd_gradient_errors'])for r in rows));print('savedbox exclusions',sum(r['excludes']for r in boxes),'/',len(boxes))
