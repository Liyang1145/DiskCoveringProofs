from fractions import Fraction as F
from pathlib import Path
import numpy as np,json
from scipy.optimize import linprog
r=F(9,40);ts=[F(226,1000)+F(154,1000)*i/34 for i in range(35)]+[F(55,100)+F(27,100)*i/39 for i in range(40)]+[F(1)];tv=np.array(list(map(float,ts)));m=len(ts);ds=np.unique(np.r_[np.linspace(0,1+float(r),12000),float(r),1-float(r)]);A=np.zeros((len(ds),m+4));rf=float(r)
for j,t in enumerate(tv):
 z=(abs(ds-t)<rf)&(ds>0);A[z,j]=np.arccos(np.clip((t*t+ds[z]**2-rf*rf)/(2*t*ds[z]),-1,1))
for i,d in enumerate(ds):
 g=0 if d<=rf else (2 if d>=1-rf else 1);A[i,m+g]=-1
extra=np.zeros((2,m+4));extra[:,m+3]=-1
for g in range(2):extra[g,m+g]=1
for B in [14,17]:
 s=linprog(np.r_[-np.pi*np.ones(m),1,0,B,25-B],A_ub=np.vstack((A,extra)),b_ub=np.zeros(len(ds)+2),A_eq=np.r_[np.ones(m),np.zeros(4)].reshape(1,-1),b_eq=[1],bounds=(0,None),method='highs')
 assert s.success
 out={'radius':str(r),'B':B,'data':[[str(t),int(round(w*1000000))] for t,w in zip(ts,s.x[:m]) if round(w*1000000)>0]}
 Path(f'round-20261030/lower/radial_9_40_B{B}.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
 print('B',B,'weights',len(out['data']),'gap',-s.fun,'maxima',s.x[m:])
