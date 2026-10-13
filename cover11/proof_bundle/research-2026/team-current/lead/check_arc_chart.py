"""Boundaryfirstflatpatch localchart coordinate calibration and reduced evaluator."""
from pathlib import Path
import math,json,numpy as np
P=Path(__file__).parent;s=(P/'check_joint_reduced.py').read_text();m="\nif __name__";assert s.count(m)==1
ns={'__file__':str(P/'check_joint_reduced.py')};exec(s.split(m)[0],ns);oldpatch=ns['patch'];reduced=ns['reduced'];R=.38;pi=math.pi;g=2*pi-16*math.asin(R)
def sectorleft(r,b,w):
 s=math.sqrt(1-r*r);c=np.array([s-2*r*math.sin(b)*math.cos(b),-2*r*math.sin(b)**2]);p1=np.array([s,-r]);p0=np.array([s*math.cos(w)-r*math.sin(w),-s*math.sin(w)-r*math.cos(w)]);v0=p0-c;v1=p1-c;cross=v0[0]*v1[1]-v0[1]*v1[0];a=math.atan2(cross,v0@v1)
 return a,float(np.linalg.norm(v0)/R)
def width(r,b):
 s=math.sqrt(1-r*r);X=-r*math.cos(2*b+math.asin(r));D=s*s-2*s*r*math.sin(b)*math.cos(b)+2*r*r*math.sin(b)**2;return 2*math.atan2(X,D)
def chart(y):
 r,b1,b2,fw1,fw3,fA,fH=y;W1=width(r,b1);W3=width(r,b2)
 if min(W1,W3)<g:return None
 w1=g+fw1*(W1-g);w3=g+fw3*(W3-g);a,u=sectorleft(r,b1,w1);c,v=sectorleft(r,b2,w3)
 if min(a,c)<=0:return None
 x=np.array([r/R,a,u,c,v,fA,fH]);pp=oldpatch(x)
 return None if pp is None else x
if __name__=='__main__':
 rng=np.random.default_rng(1260);count=0;err=0
 for _ in range(10000):
  r=rng.uniform(.375,.38);bc=math.acos(r);b1,b2=rng.uniform(bc/2,bc,2);ys=[r,b1,b2,*rng.uniform(0,1,4)];x=chart(ys)
  if x is None:continue
  pp=oldpatch(x);ee=max(abs(pp[0][3][0]-b1),abs(pp[0][4][0]-b2));err=max(err,ee);assert ee<1e-11
  assert min(ns['ns']['margins'](x))>=-1e-10
  count+=1
 out={'scope':'calibration of boundaryfirst chart, not maxproof','validcharts':count,'b_recovery_error':err};(P/'arc_chart_control.json').write_text(json.dumps(out,indent=2));print(out)
