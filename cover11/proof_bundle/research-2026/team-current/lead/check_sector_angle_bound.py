"""Symbolic chord-coordinate identity; numerical calibration of stronger necessarybound."""
from pathlib import Path
import sympy as S,json,math,random
P=Path(__file__).parent;k,h,x,y,s=S.symbols('k h x y s',real=True);H=k-x
num=H**2+y**2-h**2-2*k*H+1-x*x-y*y
assert S.expand(num)==1-k*k-h*h
assert S.expand(2*k*(k+s)-(1-s*s)-((k+s)**2-h*h))==k*k+h*h-1
rng=random.Random(844);minmargin=math.inf
for _ in range(1000):
 R=rng.uniform(.375,.37999);ss=math.sqrt(1-R*R);w=rng.uniform(.04661754,2*math.asin(R));kk=math.cos(w/2);hh=math.sin(w/2);rr=ss*math.sqrt(rng.random());t=rng.random()*2*math.pi;xx,yy=rr*math.cos(t),rr*math.sin(t)
 alpha=math.atan2(2*hh*(kk-xx),(kk-xx)**2+yy*yy-hh*hh);lb=2*math.atan(hh/(kk+ss));assert alpha>=lb-1e-14;minmargin=min(minmargin,alpha-lb)
(P/'sector_angle_bound_control.json').write_text(json.dumps({'scope':'exact cotidentity and strongerbound algebra;1000numeric calibrationpoints not continuumproof','symbolic_residuals':['1-k²-h²','k²+h²-1'],'min_numeric_margin':minmargin},indent=2));print('twoexactidentities;1000controls;minmargin',minmargin)
