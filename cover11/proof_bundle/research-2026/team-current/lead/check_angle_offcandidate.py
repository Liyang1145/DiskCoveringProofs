"""Independent coordinate controls, including NONCYCLIC boundaries: circle constraints are not identities."""
from pathlib import Path
import numpy as np,math,json
P=Path(__file__).parent
ns2={'__file__':str(P/'check_angle_only.py')};exec((P/'check_angle_only.py').read_text().split("a=ns['x0'][:42]")[0],ns2)
ns=ns2['ns'];shape=ns2['shape'];base=ns['c'];faces=ns['faces'];rng=np.random.default_rng(839);rows=[]
for k in range(20):
 c=base+rng.uniform(-.0002,.0002,base.shape);angs=[];rad=[];ps=[];bs=[]
 for f in faces:
  p=c[f];o=np.linalg.solve(2*(p[1:]-p[0]),np.sum(p[1:]**2,axis=1)-sum(p[0]**2));rad.append(np.linalg.norm(o-p[0]))
  for i in range(3):
   u=p[(i+1)%3]-p[i];v=p[(i+2)%3]-p[i];angs.append(math.acos(np.clip(u@v/np.linalg.norm(u)/np.linalg.norm(v),-1,1)))
 for i in range(9):
  j=(i+1)%9;mid=(c[i]+c[j])/2;d=np.linalg.norm(c[j]-c[i]);u=np.array([(c[j]-c[i])[1],-(c[j]-c[i])[0]])/d
  lam=-mid@u+math.sqrt((mid@u)**2+1-mid@mid)
  if k>=10:lam+=rng.uniform(-.001,.001)
  p=mid+lam*u;ps.append(p);bs.append(math.atan2(d/2,lam));rad.append(np.linalg.norm(p-c[i]))
 R,con,z=shape(np.r_[angs,bs]);ps=np.array(ps);gam=np.exp(z['logg']);physical_scale=rad[0];ell=np.linalg.norm(ps-np.roll(ps,1,axis=0),axis=1)/physical_scale
 assert max(abs(gam-np.array(rad)/physical_scale))<1e-12 and max(abs(con[:15]))<1e-12
 assert min(z['w'])>0 and max(z['w'])<math.pi
 v=(ps-np.roll(ps,1,axis=0))/(ell[:,None]*physical_scale);q=2*np.sin(z['w']/2)
 erclosure=float(np.linalg.norm(np.sum(q[:,None]*v,axis=0)));assert erclosure<1e-12
 circle=float(max(abs(con[15:])))
 if k<10:assert circle<1e-12 and abs(R-max(rad))<1e-12
 else:assert circle>1e-5
 rows.append({'case':k,'cyclic':k<10,'shape_objective':R,'actual_max_local_radius':max(rad),'circle_residual':circle,'canonical_vector_closure_error':erclosure})
(P/'angle_offcandidate_control.json').write_text(json.dumps({'scope':'20independent actual planar coordinate examples, 10unitcyclic10noncyclic; numeric calibration not proof','rows':rows},indent=2));print('20 independent coordinate controls passed; noncyclic ratio residuals',[round(r['circle_residual'],6) for r in rows[10:]])
