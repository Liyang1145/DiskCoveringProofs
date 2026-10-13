"""Calibrate Cartesian second AD versus finite differences; test integratingfactor on legal samples."""
from pathlib import Path
import face_second_jet as f
from interval_joint_patch import I,uf,lf
import random,math,json
rng=random.Random(868);rows=[]
for j in [0,1]:
 points=[];attempts=0
 while len(points)<160 and attempts<5000:
  attempts+=1;r=rng.uniform(.375,.38);b1=rng.uniform(1,math.acos(r));b2=rng.uniform(1,math.acos(r));d=rng.uniform(-b2,b1);x=[I(str(v))for v in [r,b1,b2,d]]
  if not f.legal(x,j):continue
  a=f.objective(x,j);gp=(lf(a.d)+uf(a.d))/2;gh=(lf(a.h)+uf(a.h))/2
  points.append({'point':[r,b1,b2,d],'d':gp,'h':gh,'weighted':gh+(1 if j==0 else -1)*8*gp})
 # FD highprecision interval differencing at a subset; h=1e-4 error O(h²).
 for p in points[:5]:
  x=[I(str(v))for v in p['point']];h=I('1e-4');xp=x.copy();xm=x.copy();xp[3]+=h;xm[3]-=h
  fd=(f.objective(xp,j).v-2*f.objective(x,j).v+f.objective(xm,j).v)/(h*h);p['fd_second']=str(fd)
 low=max([-p['h']/((1 if j==0 else -1)*p['d']) for p in points if (1 if j==0 else -1)*p['d']>0]+[-1e9]);high=min([-p['h']/((1 if j==0 else -1)*p['d']) for p in points if (1 if j==0 else -1)*p['d']<0]+[1e9])
 rows.append({'j':j,'k_interval':[low,high],'points':points,'count':len(points),'min_weighted':min(t['weighted']for t in points),'worst':sorted(points,key=lambda p:p['weighted'])[:5],'calibrations':points[:5]})
Path(__file__).with_name('face_integrating_probe.json').write_text(json.dumps(rows,indent=2));print([(r['j'],r['count'],r['min_weighted'],r['worst'][0])for r in rows])
