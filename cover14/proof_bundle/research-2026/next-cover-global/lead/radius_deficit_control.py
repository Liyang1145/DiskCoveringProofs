"""Actualcover control for analytic radiusdeficit lemma, both edgeandface forms."""
from face_angle_control import C,W,R,E,gammas,faces,angle,P
import math,json
U=.33173203427623414
loss={};beta={};out=[]
for e,fs in E.items():
 if len(fs)!=2:continue
 f,g=fs;b=angle(W[f]-C[e[0]],W[g]-C[e[0]]);de=(gammas[f,e]-gammas[g,e])/2;actual=(U*U-R[f]*R[g])*math.sin(b);lower=U*U*(1-math.cos(b))*abs(de);assert actual>=lower-2e-15;loss[e]=actual;beta[e]=b;out.append({'edge':e,'actual_deficit':actual,'lower':lower})
fr=[]
from itertools import combinations
for f,vs in enumerate(faces):
 ee=[tuple(sorted(e))for e in combinations(vs,2)]
 if not all(e in loss for e in ee):continue
 actual=sum(loss[e]for e in ee);lower=U*U/2*min(1-math.cos(beta[e])for e in ee)*abs(sum(beta[e]for e in ee)-math.pi);assert actual>=lower-3e-15;fr.append({'face':f,'actual_deficit':actual,'lower':lower})
(P/'radius-deficit-control.json').write_text(json.dumps({'status':'numeric_actualcover_calibration_only','edges':out,'faces':fr},indent=2));print('radiusdeficitcontrols',len(out),len(fr))
