"""Interval geometry audit on repaired TC root box. Active identities from res5 must still be audited analytically.
Outputs box margins, mapping to11 Delaunay faces; no automatic claim registration.
"""
from pathlib import Path
import json,sys,numpy as np
from mpmath import mp,iv
P=Path(__file__).parent
sys.path.insert(0,str(P));import repair_tc_krawczyk as K
mp.dps=60;iv.dps=50
j=json.loads((P/'repaired_tc_krawczyk.json').read_text());cert=j['certificate'];rad=float.fromhex(cert['radius_hex']);u=[iv.mpf(float.fromhex(v))+iv.mpf([-rad,rad]) for v in cert['center_hex']];z=u[:7];r=z[6]
a4=iv.pi-2*sum(z[:4]);a=[z[0],z[1],z[2],z[3],a4,z[3],z[2],z[1],z[0]]
rho=[iv.cos(v)-iv.sqrt(r*r-iv.sin(v)**2) for v in a];th=[iv.mpf(0)]*9
for k in range(5,9):th[k]=th[k-1]+a[k-1]+a[k]
for k in range(3,-1,-1):th[k]=th[k+1]-(a[k]+a[k+1])
c=[(rho[k]*iv.cos(th[k]),rho[k]*iv.sin(th[k])) for k in range(9)]+[(z[4],iv.mpf(0)),(z[5],iv.mpf(0))]
B=[(iv.cos(th[k]+a[k]),iv.sin(th[k]+a[k])) for k in range(9)]
p=[tuple(c[k][v]+c[(k+1)%9][v]-B[k][v] for v in range(2)) for k in range(9)]
def sqdist(a,b):return sum((a[k]-b[k])**2 for k in range(2))
# The five outer distance square-roots in res5 must also stay smooth.
for edge,hub in [(1,10),(2,9),(3,9),(8,10)]:
 assert sqdist(p[edge],c[hub])>iv.mpf('0.14')
waist=((z[4]+z[5])/2,iv.sqrt(r*r-((z[5]-z[4])/2)**2))
assert sqdist(waist,c[6])>iv.mpf('0.14')
assert z[4]-z[5]>iv.mpf('0.4')
# Boundary switch branches persist as actual nearest-site critical values.
assert all(sqdist(B[k],c[j])-r*r>iv.mpf('0.01') for k in range(9) for j in range(11) if j not in [k,(k+1)%9])
def mid(x):return float((mp.mpf(x.a)+mp.mpf(x.b))/2)
def low(x):return float(mp.mpf(x.a))
def high(x):return float(mp.mpf(x.b))
cm=np.array([[mid(v) for v in cc] for cc in c]);faces=[[2,9,10],[6,9,10]]+[[k,(k+1)%9,9 if 2<=k<=5 else 10] for k in range(9)];rows=[]
# Fixed combinatorial object, independent of a numerical triangulator.
from collections import Counter
edgecounts=Counter(tuple(sorted((f[i],f[(i+1)%3]))) for f in faces for i in range(3))
hull={tuple(sorted((k,(k+1)%9))) for k in range(9)}
assert len(edgecounts)==21 and all(v==(1 if e in hull else 2) for e,v in edgecounts.items())
assert all(iv.mpf('0.28')<v and v<iv.mpf('0.4') for v in a)
assert all(iv.mpf(0)<v and v<iv.mpf(1) for v in rho)
for f in faces:
 pp=cm[f];v=np.linalg.solve(2*(pp[1:]-pp[0]),np.sum(pp[1:]**2,axis=1)-np.sum(pp[0]**2));rr=np.linalg.norm(v-pp[0]);rings=sorted(k for k in f if k<9);hubs=sorted(k for k in f if k>=9)
 if len(rings)==2:
  edge=next(i for i in range(9) if set(rings)=={i,(i+1)%9});hub=hubs[0];pin=p[edge]
  slack=sqdist(pin,c[hub])-r*r
  active=(edge,hub-9) in [(1,1),(2,0),(3,0),(4,0),(5,0),(6,1),(8,1)]
  if active:cc=pin;rad_sq=r*r
  else:
   # enclosure of circumcenter for slack faces via explicit determinant linear solve
   A=[[2*(c[f[i+1]][k]-c[f[0]][k]) for k in range(2)] for i in range(2)]
   d=[sqdist(c[f[i+1]],(0,0))-sqdist(c[f[0]],(0,0)) for i in range(2)];det=A[0][0]*A[1][1]-A[0][1]*A[1][0]
   cc=((d[0]*A[1][1]-A[0][1]*d[1])/det,(A[0][0]*d[1]-d[0]*A[1][0])/det);rad_sq=sqdist(cc,c[f[0]])
 else:
  edge=None;active=True;h=iv.sqrt(r*r-((z[5]-z[4])/2)**2);m=(z[4]+z[5])/2;cc=(m,h if cm[rings[0],1]>0 else -h);rad_sq=r*r;slack=sqdist(cc,c[rings[0]])-r*r
 empty=min(low(sqdist(cc,c[k])-rad_sq) for k in range(11) if k not in f)
 assert all(sqdist(cc,c[k])-rad_sq>iv.mpf('0.15') for k in range(11) if k not in f)
 assert sqdist(cc,(0,0))<iv.mpf('0.4')
 if not active:assert rad_sq-r*r<iv.mpf('-0.0008')
 assert abs((c[f[1]][0]-c[f[0]][0])*(c[f[2]][1]-c[f[0]][1])-(c[f[1]][1]-c[f[0]][1])*(c[f[2]][0]-c[f[0]][0]))>iv.mpf('0.14')
 rows.append({'face':f,'edge':edge,'active':active,'numeric_radius':rr,'empty_margin':empty,'root_identity_residual_interval':[low(slack),high(slack)],'radius_minus_r_squared_interval':[low(rad_sq-r*r),high(rad_sq-r*r)]})
hub_margin=min(low((1-r)**2-sqdist(c[k],(0,0))) for k in [9,10]);assert hub_margin>0
angle_margin=min(low(r*r-iv.sin(v)**2) for v in a);assert angle_margin>0
def cross(a,b,d):return (b[0]-a[0])*(d[1]-a[1])-(b[1]-a[1])*(d[0]-a[0])
hull_margin=min(low(cross(c[k],c[(k+1)%9],c[jj])) for k in range(9) for jj in range(11) if jj not in [k,(k+1)%9]);assert hull_margin>0
assert all((1-r)**2-sqdist(c[k],(0,0))>iv.mpf('0.3') for k in [9,10])
assert all(r*r-iv.sin(v)**2>iv.mpf('0.001') for v in a)
assert all(cross(c[k],c[(k+1)%9],c[jj])>iv.mpf('0.05') for k in range(9) for jj in range(11) if jj not in [k,(k+1)%9])
assert len(rows)==2*11-9-2
out={'hull_orientation_margin':hull_margin,'scope':'interval geometry around unique TC root; active identities require analytic root equations, not intervals containing zero','faces':rows,'hub_norm_squared_margin':hub_margin,'root_branch_margin':angle_margin,'boundary_arc_halfwidth_min':min(low(v) for v in a),'boundary_arc_halfwidth_max':max(high(v) for v in a)}
(P/'tc_root_geometry.json').write_text(json.dumps(out,indent=2));print('11 faces',len(rows),'active',sum(v['active'] for v in rows),'hub margin',hub_margin,'empty margin',min(v['empty_margin'] for v in rows))
