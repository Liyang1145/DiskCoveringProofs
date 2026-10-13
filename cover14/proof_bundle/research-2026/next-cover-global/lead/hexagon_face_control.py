"""Independent shoelace representation calibration; numeric only."""
from boundary_radius_control import *
def cross(u,v):return u[0]*v[1]-u[1]*v[0]
def signedarea(V):return sum(cross(V[i],V[(i+1)%len(V)])for i in range(len(V)))/2
out=[]
for f,ids in enumerate(faces):
 ids=list(ids)
 if cross(C[ids[1]]-C[ids[0]],C[ids[2]]-C[ids[0]])<0:ids[1],ids[2]=ids[2],ids[1]
 polygon=[];radii=[]
 for i in range(3):
  u,v=ids[i],ids[(i+1)%3];e=tuple(sorted((u,v)));fs=E[e];other=[j for j in fs if j!=f];A=W[other[0]]if other else anchors[e];polygon.extend([C[u],A]);radii.append(float(np.linalg.norm(A-C[u])))
 actual=sum(U*U*math.sin(beta[tuple(sorted(e))])-loss[tuple(sorted(e))]for e in combinations(ids,2));poly=signedarea(polygon);energy=sum(float(np.dot(polygon[(i+1)%6]-polygon[i],polygon[(i+1)%6]-polygon[i]))for i in range(6));cap=math.sqrt(3)/4*energy
 assert abs(actual-poly)<1e-14 and actual<=cap+1e-14
 out.append({'face':f,'paired_area':float(actual),'hexagon_signed_area':float(poly),'cap_energy':cap,'universal_cap':3*math.sqrt(3)/2*U*U,'radius_energy_residual':energy-2*sum(t*t for t in radii)})
# Equilateral six-sided known answer, Fourier inequality equality.
poly=[np.array([U*math.cos(k*math.pi/3),U*math.sin(k*math.pi/3)])for k in range(6)];assert abs(signedarea(poly)-3*math.sqrt(3)/2*U*U)<1e-14
(P/'hexagon-face-control.json').write_text(json.dumps({'status':'numeric_shoelace_geometry_control_not_proof','rows':out},indent=2));print('hexagon controls',len(out),'maximum area residual',max(abs(x['paired_area']-x['hexagon_signed_area'])for x in out))
