"""Actualcover control of virtual opposite angles for boundary facets."""
from face_angle_control import *
anchors={tuple(sorted(a['owners'])):np.array([math.cos(float(a['theta'])),math.sin(float(a['theta']))])for a in G['anchors']}
beta={};loss={};out=[]
U=.33173203427623414
for e,fs in E.items():
 f=fs[0];u,v=C[list(e)];g=gammas[f,e]
 if len(fs)==2:A=W[fs[1]];ra=R[fs[1]]
 else:A=anchors[e];ra=np.linalg.norm(A-u)
 b=angle(W[f]-u,A-u);gv=math.pi-b-g;de=(g-gv)/2
 assert gv>=-1e-14
 residual=R[f]*math.sin(g)-ra*math.sin(gv)
 assert abs(residual)<2e-14
 actual=(U*U-R[f]*ra)*math.sin(b);lower=U*U*(1-math.cos(b))*abs(de)
 assert actual>=lower-2e-14;beta[e]=b;loss[e]=actual
 if len(fs)==1:out.append({'edge':e,'beta':b,'physical_gamma':g,'virtual_gamma':gv,'shared_length_residual':float(residual),'deficit':float(actual),'lower':lower})
fr=[]
for f,vs in enumerate(faces):
 ee=[tuple(sorted(e))for e in combinations(vs,2)];lower=U*U/2*min(1-math.cos(beta[e])for e in ee)*abs(sum(beta[e]for e in ee)-math.pi);actual=sum(loss[e]for e in ee);assert actual>=lower-2e-14;fr.append({'face':f,'actual':float(actual),'lower':lower})
(P/'boundary-radius-control.json').write_text(json.dumps({'status':'numeric_actualcover_control_only','boundary_edges':out,'all_faces':fr},indent=2));print('boundaryvirtualanglecontrols',len(out),'allfaces',len(fr))
