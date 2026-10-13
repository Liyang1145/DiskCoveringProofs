"""Two coordinate boundary expression calibration; allpoints saved."""
import math,json,random
from pathlib import Path
import numpy as np
P=Path(__file__).parent;z=json.loads((P/'joint_nested_frozen.json').read_text())['z'];R=.38;gen=random.Random(862);rows=[]
for _ in range(800):
 r=gen.uniform(.375,.38);b1=gen.uniform(1,math.acos(r));b2=gen.uniform(1,math.acos(r));de=gen.uniform(-b2,b1);s=math.sqrt(1-r*r);A=b1-de;B=b2+de
 for j in range(4):
  if j==0:H=2*r*math.sin(b1+A)
  elif j==1:H=2*r*math.sin(b2+B)
  else:
   rad=(1-r)**2-s*s*math.sin(de)**2
   if rad<0:continue
   H=s*math.cos(de)+(1 if j==2 else -1)*math.sqrt(rad)
  margins=[H-(s-1+r),2*r-H,2*r*math.sin(b1+A)-H,2*r*math.sin(b2+B)-H,-H*H+2*s*math.cos(de)*H-2*r*(1-r)]
  if min(margins)<-1e-12:continue
  v=H*math.cos(de);t=H*math.sin(de);cart=r*(math.sin(b1)**2+math.sin(b2)**2)*v+r*(math.sin(b2)*math.cos(b2)-math.sin(b1)*math.cos(b1))*t;polar=(z[3]-z[1])*de+H*r*(math.sin(b1)*math.sin(A)+math.sin(b2)*math.sin(B));ident=[]
  for i,(b,ang,a,bb,gg,sg)in enumerate([(b1,A,z[1]-z[9],-z[16],-z[78],-1),(b2,B,z[3]-z[9],z[20],z[82],1)]):
   X=v-r*math.sin(2*b);Y=2*r*math.sin(b)**2+sg*t;ec=math.hypot(X,Y)/(2*R);cart+=a*math.atan2(Y,X)+bb*ec*ec+gg*ec
   xx=H-2*r*math.sin(b)*math.cos(ang);yy=2*r*math.sin(b)*math.sin(ang);ep=math.hypot(xx,yy)/(2*R);phi=math.atan2(yy,xx)
   if i==j:ident.append([ep-r*math.sin(ang)/R,phi-b]);ep=r*math.sin(ang)/R;phi=b
   polar+=a*phi+bb*ep*ep+gg*ep
  assert abs(cart-polar)<2e-13
  rows.append({'r_b1_b2_delta':[r,b1,b2,de],'branch':j,'H':H,'margin':margins,'cartesian':cart,'saturated':polar,'residual':cart-polar,'identity_residual':ident})
assert len(rows)>100
out={'scope':'calibrationonly; savedpointwisecontrols notcontinuumproof','points':len(rows),'maxerror':max(abs(q['residual'])for q in rows),'branches':{j:sum(q['branch']==j for q in rows)for j in range(4)},'rows':rows};(P/'saturated_identity_control.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items()if k!='rows'})
