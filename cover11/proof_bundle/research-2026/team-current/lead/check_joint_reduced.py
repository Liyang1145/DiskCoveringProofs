"""Independent edge-length/area representation of 7factor objective, zero kap/lambda case."""
from pathlib import Path
import math,json,numpy as np
P=Path(__file__).parent;s=(P/'exchange_joint_patch.py').read_text();mark='\nrows=[]';assert s.count(mark)==1
ns={'__file__':str(P/'exchange_joint_patch.py')};exec(s.split(mark)[0],ns);patch=ns['patch'];catom=ns['catom'];R=.38;pi=math.pi
z=np.array(json.loads((P/'joint_patch_frozen_v2.json').read_text())['z']);assert np.all(z[50:73]==0)

def reduced(x):
 base,args,geo=patch(x);t,a,u,c,v=x[:5];b1,b2=base[3][0],base[4][0];A,B,H,r=geo['A'],geo['B'],geo['H'],geo['r'];D1,D2=2*r*math.sin(b1),2*r*math.sin(b2)
 w1,L1,T1=ns['ns']['ns']['sector'](a,u,t);w3,L3,T3=ns['ns']['ns']['sector'](c,t,v);w2=2*math.asin(r);hub1,hub2=args[0][0],args[1][0]
 e1=math.sqrt(H*H+D1*D1-2*H*D1*math.cos(A))/(2*R);e3=math.sqrt(H*H+D2*D2-2*H*D2*math.cos(B))/(2*R)
 area=.5*H*(D1*math.sin(A)+D2*math.sin(B))+.5*r*r*(math.sin(2*b1)+math.sin(2*b2))+.5*R*R*t*(u*math.sin(a)+v*math.sin(c))+sum((w-math.sin(w))/2 for w in [w1,w2,w3])
 val=area+pi*(z[113]+z[114]-z[2])+z[1]*(b1-a-pi+A+hub1)+z[3]*(b2-c-pi+B+hub2)-z[9]*(hub1+hub2)-z[16]*e1*e1-z[78]*e1+z[20]*e3*e3+z[82]*e3-z[34]*u*u-z[96]*u-z[39]*v*v-z[101]*v+z[112]*(L1+w1/2)+z[115]*(T3+w3/2)
 return val
if __name__=='__main__':
 rng=np.random.default_rng(1250);n=0;err=0
 for _ in range(20000):
  x=np.array([rng.uniform(l,h)for l,h in ns['bounds']])
  if patch(x) is None:continue
  v,m=catom(x);e=abs(reduced(x)-(v+m@z));err=max(err,e);assert e<1e-10;n+=1
 out={'scope':'independent area/edge expression control, not continuummax','patches':n,'max_difference':err};(P/'joint_reduced_control.json').write_text(json.dumps(out,indent=2));print(out)
