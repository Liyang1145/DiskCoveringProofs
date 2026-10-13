"""Positive FH' over an explicitouterneighborhood and entireprojectedHfiber."""
import interval_patch_delta as f
import interval_joint_patch as k
from interval_joint_patch import I,iv,R,z,lf,uf
from pathlib import Path
import json,hashlib
P=Path(__file__).parent
# Rationalbox aroundcandidate; physicalrupper .38
outer=[I('0.379','0.38'),I('1.105','1.108'),I('1.068','1.071'),I('0.035','0.040')]
r,b1,b2,de=outer;A=b1-de;B=b2+de;st=f.setup(outer);lo,hi=st[1][2][1]
def derivative(H):
 val=I(0)
 for b,th,az,bz,gz in [(b1,A,z[1]-z[9],-z[16],-z[78]),(b2,B,z[3]-z[9],z[20],z[82])]:
  D=2*r*iv.sin(b);yy=D*iv.sin(th);xx=H-D*iv.cos(th);Q=xx**2+yy**2
  assert Q.a>0
  val+=yy/2-az*yy/Q+bz*xx/(2*R*R)+gz*xx/(2*R*iv.sqrt(Q))
 return val
cuts=[lo+(hi-lo)*j/64 for j in range(65)];cuts[0]=lo;cuts[-1]=hi;vals=[derivative(I(a,b))for a,b in zip(cuts,cuts[1:])];lower=min(lf(v)for v in vals);assert lower>0
# Showhubnormupperinactive throughoutbox: itslower exceedsbothfaceupperupper
s=iv.sqrt(1-r*r);cs=iv.cos(de);disc=s*s*cs*cs-2*r*(1-r);assert disc.a>0
hubup=s*cs+iv.sqrt(disc);faceups=[2*r*iv.sin(b1+A),2*r*iv.sin(b2+B)];assert all(hubup.a>v.b for v in faceups)
out={'scope':'explicit4Douterbox and allactualHfibers therein; notglobal','outer_strings':[['.379','.38'],['1.105','1.108'],['1.068','1.071'],['.035','.040']],'H_projection':[lo,hi],'derivative_lower':lower,'derivative_upper':max(uf(v)for v in vals),'subintervals':64,'hubupper_lower':lf(hubup),'faceupper_upper':max(uf(v)for v in faceups),'conclusion':'FH strictlyincreasing; maximum atmin(2r sin(2b1-delta),2r sin(2b2+delta))','coefficient_sha256':hashlib.sha256(k.frozen.read_bytes()).hexdigest()};(P/'h_monotone_box_certificate.json').write_text(json.dumps(out,indent=2));print(out)
