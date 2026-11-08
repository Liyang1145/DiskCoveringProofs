import json,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent; data=json.loads((p/'rational_geometry.json').read_text(encoding='utf8')); faces=data['faces']; anchors=data['boundary_anchors'];edges=[]
for i,f in enumerate(faces):
 for c in f:edges.append({'witness':f'F{i:02d}','center':f'C{c:02d}','kind':'interior-circumcenter'})
for i in range(16):
 for c in (i,(i+1)%16):edges.append({'witness':f'B{i:02d}','center':f'C{c:02d}','kind':'rational-boundary-anchor'})
assert len(edges)==134
obj={'source':'rational_geometry.json', 'source_sha256':hashlib.sha256((p/'rational_geometry.json').read_bytes()).hexdigest(), 'center_count':26,'interior_face_count':34,'boundary_anchor_count':16,'incidence_count':len(edges),'face_vertices':faces,'boundary_center_order':list(range(16)),'incidences':edges,'warning':'Incidences establish valid covering witness constraints; they are not necessarily equal-length contacts. Four faces have circumradius < 0.232. This is not proved identical to the archived 134-rod model or its isolated root.'}
(p/'incidence_graph.json').write_text(json.dumps(obj,indent=2)+'\n',encoding='utf8')
