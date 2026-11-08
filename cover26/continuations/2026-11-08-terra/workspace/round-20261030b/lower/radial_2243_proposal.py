from fractions import Fraction as F
from pathlib import Path
import numpy as np,json
from scipy.optimize import linprog
r=F(2243,10000);rf=float(r);ts=[F(2245,10000)+F(1555,10000)*i/49 for i in range(50)]+[F(52,100)+F(30,100)*i/54 for i in range(55)]+[F(1)];tv=np.array(list(map(float,ts)));m=len(ts);ds=np.unique(np.r_[np.linspace(0,1+rf,16000),rf,1-rf]);A=np.zeros((len(ds),m+4))
for j,t in enumerate(tv):
 z=(abs(ds-t)<rf)&(ds>0);A[z,j]=np.arccos(np.clip((t*t+ds[z]**2-rf*rf)/(2*t*ds[z]),-1,1))
for i,d in enumerate(ds):
 g=0 if d<=rf else 2 if d>=1-rf else 1;A[i,m+g]=-1
ex=np.zeros((2,m+4));ex[:,m+3]=-1
for g in range(2):ex[g,m+g]=1
for B in range(14,18):
 s=linprog(np.r_[-np.pi*np.ones(m),1,0,B,25-B],A_ub=np.vstack([A,ex]),b_ub=np.zeros(len(ds)+2),A_eq=np.r_[np.ones(m),np.zeros(4)].reshape(1,-1),b_eq=[1],bounds=(0,None),method='highs',options={'time_limit':15})
 if not s.success:print(B,'PENDING LP',flush=True);continue
 d={'radius':str(r),'B':B,'data':[[str(t),round(w*1000000)] for t,w in zip(ts,s.x[:m]) if round(w*1000000)>0]};Path(f'round-20261030b/lower/radial_2243_B{B}.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf8')
 print(B,'gap',-s.fun,'n',len(d['data']),flush=True)
