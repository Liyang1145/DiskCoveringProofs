"""C861 boundarykernel with exact necessary angulararccontractors."""
import interval_hub_boundary as base
import interval_patch_delta as fibers
from interval_joint_patch import I,iv,z,R,pi,acos,lf,uf

def arc_domains(disks,j):
 cx,cy,rho=disks[j];dom=[(lf(-pi),uf(pi))]
 for i,(dx,dy,rr)in enumerate(disks):
  if i==j:continue
  X=dx-cx;Y=dy-cy;d2=X*X+Y*Y
  if d2.a<=0:continue # coincident/uncertain centers: skip onlythiscontractor
  d=iv.sqrt(d2);q=(rho*rho+d2-rr*rr)/(2*rho*d)
  if q.a>1:return []
  if q.a<=-1:continue
  width=acos(I(q.a));arg=iv.atan2(Y,X);interval=arg+I(-width.b,width.b)
  allowed=[]
  for shift in [-1,0,1]:
   arc=interval+2*shift*pi
   for lo,hi in dom:
    l=max(lo,lf(arc));h=min(hi,uf(arc))
    if l<=h:allowed.append((l,h))
  allowed.sort();dom=[]
  for l,h in allowed:
   if dom and l<=dom[-1][1]:dom[-1]=(dom[-1][0],max(h,dom[-1][1]))
   else:dom.append((l,h))
  if not dom:return []
 return dom

def setup(outer):
 st=base.setup(outer)
 if st is None:return None
 K,ws,cs=st;r,b1,b2=outer;s=iv.sqrt(1-r*r)
 disks=[(r*iv.sin(2*b1),-r*iv.cos(2*b1),r),(r*iv.sin(2*b2),r*iv.cos(2*b2),r),(s,I(0),1-r)]
 arcs=[]
 for j,(fun,_)in enumerate(cs):
  arcs.extend((fun,dom)for dom in arc_domains(disks,j))
 return K,ws,arcs

def bound(outer,tol=1e-5,maxeval=129):
 assert all(b.a>=1 for b in outer[1:])
 st=setup(outer)
 if st is None:return None
 K,ws,cs=st
 if not cs:return None
 ww=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in ws];cc=[fibers.envelope(fun,dom,tol,maxeval)for fun,dom in cs]
 if any(row['upper']==-float('inf')for row in ww)or all(row['upper']==-float('inf')for row in cc):return None
 total=K+sum((I(row['upper'])for row in ww),I(0))+I(max(row['upper']for row in cc))
 return {'upper':uf(total),'widths':ww,'circles':cc,'arc_domains':[dom for fun,dom in cs]}
