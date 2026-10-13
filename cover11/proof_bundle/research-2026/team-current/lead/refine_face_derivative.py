from certify_face_derivative import ev
from interval_joint_patch import I
import json,heapq,time
D=json.load(open('face_deriv_probe.json'))
# replay bad boxes and recursively bisect widest coordinate, retaining only boxes whose derivative interval is nonpositive/straddles
bad=[];cert=0;work=[]
for q in D['bad']:
 work.append((0,[I(*x) for x in q['box']]))
while work:
 dep,x=work.pop();v=ev(x)
 if v is None: continue
 if v.a>0:cert+=1;continue
 if dep>=11:
  bad.append({'box':[(float(y.a),float(y.b)) for y in x],'dv':str(v)});continue
 k=max(range(4),key=lambda i:float(x[i].b-x[i].a));m=(x[k].a+x[k].b)/2
 for side in [0,1]:
  y=x.copy();y[k]=I(x[k].a,m) if side==0 else I(m,x[k].b)
  work.append((dep+1,y))
print({'initial_bad':len(D['bad']),'certified_subboxes':cert,'remaining':len(bad)});json.dump(bad,open('face_deriv_refined_bad.json','w'),indent=2)
