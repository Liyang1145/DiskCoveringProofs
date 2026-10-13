"""Independent numeric calibration of boundarycenter elimination and hA sign."""
from boundary_radius_control import *
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
if __name__=='__main__':
 bedges=[e for e in E if len(E[e])==1];bverts=sorted(set(v for e in bedges for v in e));out=[]
 for v in bverts:
  es=[e for e in bedges if v in e];A,B=[anchors[e]for e in es]
  if cross(A,B)<0:A,B=B,A
  e=(B-A)/np.linalg.norm(B-A);n=np.array([-e[1],e[0]]);L=np.linalg.norm(B-A);a=np.linalg.norm(A-C[v]);b=np.linalg.norm(B-C[v]);s=(a*a-b*b+L*L)/(2*L);h=math.sqrt(max(0,a*a-s*s));pred=A+s*e+h*n;out.append({'site':v,'center_error':float(np.linalg.norm(pred-C[v])),'height':h})
 rows=[]
 for e in bedges:
  f=E[e][0];u,v=e;w=next(i for i in faces[f]if i not in e);d=C[v]-C[u]
  if cross(d,C[w]-C[u])<0:u,v=v,u;d=-d
  n=np.array([-d[1],d[0]])/np.linalg.norm(d);m=(C[u]+C[v])/2;hA=float((anchors[e]-m)@n);hO=float((W[f]-m)@n);rows.append({'edge':e,'hA':hA,'hO':hO,'gammaA':math.pi/2+math.atan2(2*hA,np.linalg.norm(d))});assert hA<0 and hO>hA
 assert max(z['center_error']for z in out)<1e-12
 (P/'boundary-parameter-control.json').write_text(json.dumps({'status':'numeric_calibration_only','center_reconstruction':out,'boundary_height':rows},indent=2));print('max centererror',max(z['center_error']for z in out),'max hA',max(z['hA']for z in rows))
