"""Alternative exact contact formulas; same directed interval AD, different algebraic representation."""
import local_sosc_certificate as b

def circum(p,q,v):
 u=[q[k]-p[k]for k in range(2)];w=[v[k]-p[k]for k in range(2)];t=[v[k]-q[k]for k in range(2)]
 det=u[0]*w[1]-u[1]*w[0]
 return b.norm(u)*b.norm(w)*b.norm(t)/(4*det*det)

def boundary(p,q,sign):
 # A=base+sign rad perp(dv), scalar distance 1+|p|²-2A dotp.
 dv=[q[k]-p[k]for k in range(2)];nn=b.norm(dv);k=(b.norm(q)-b.norm(p))/2
 base=[v*k/nn for v in dv];rad=((1-b.norm(base))/nn).sqrt()
 return 1+b.norm(p)-2*(base[0]*p[0]+base[1]*p[1]+sign*rad*(-dv[1]*p[0]+dv[0]*p[1]))

if __name__=='__main__':
 import json
 diffs=[]
 for kk,entry in enumerate(b.g['anchors']+b.g['faces']):
  ids=entry['owners']if kk<10 else entry['ids'];ps=[[b.J.var(b.C[i][j],2*l+j)for j in range(2)]for l,i in enumerate(ids)]
  if kk<10:
   p,q=[b.C[i]for i in ids];dv=[q[j]-p[j]for j in range(2)];ba=[v*((b.norm(q)-b.norm(p))/2/b.norm(dv))for v in dv];an=b.anchors[kk];sg=-dv[1]*(an[0]-ba[0])+dv[0]*(an[1]-ba[1]);assert sg.lo*sg.hi>0;sign=1 if sg.lo>0 else -1
   f=boundary(*ps,sign);old=b.boundary(*ps,sign)
  else:f=circum(*ps);old=b.circum(*ps)
  a=[f.v]+f.g+sum(f.h,[]);c=[old.v]+old.g+sum(old.h,[])
  assert all(max(x.lo,y.lo)<=min(x.hi,y.hi)for x,y in zip(a,c))
  diffs.append(max(abs(b.mid(x)-b.mid(y))for x,y in zip(a,c)))
 out={'status':'root_interval_overlap_controls_not_independent_AD','contacts':len(diffs),'max_midpoint_difference':max(diffs)};(b.P/'local-contact-alternative-control.json').write_text(json.dumps(out,indent=2));print(out)
