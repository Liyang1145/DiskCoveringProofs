from fractions import Fraction as F
from pathlib import Path
import numpy as np,json
from scipy.optimize import linprog
r=F(28,125);ts=[F(225,1000)+F(155,1000)*i/34 for i in range(35)]+[F(55,100)+F(27,100)*i/39 for i in range(40)]+[F(1)]
tv=np.array(list(map(float,ts)));m=len(ts);ds=np.unique(np.r_[np.linspace(0,1+float(r),20000),float(r),1-float(r)]);A=np.zeros((len(ds),m+4));rf=float(r)
for j,t in enumerate(tv):
 z=(abs(ds-t)<rf)&(ds>0);A[z,j]=np.arccos(np.clip((t*t+ds[z]**2-rf*rf)/(2*t*ds[z]),-1,1))
for i,d in enumerate(ds):
 g=0 if d<=rf else (2 if d>=1-rf else 1);A[i,m+g]=-1
extra=np.zeros((3,m+4));extra[:,m+3]=-1
for g in range(3):extra[g,m+g]=1
s=linprog(np.r_[-np.pi*np.ones(m),1,0,14,11],A_ub=np.vstack((A,extra)),b_ub=np.zeros(len(ds)+3),A_eq=np.r_[np.ones(m),np.zeros(4)].reshape(1,-1),b_eq=[1],bounds=(0,None),method='highs')
assert s.success
out={'radius':str(r),'weight_scale':1000000,'data':[[str(t),int(round(w*1000000))] for t,w in zip(ts,s.x[:m]) if round(w*1000000)>0], 'note':'Numerical proposal only, rigorous validity requires separate exact verifier'}
Path('round-20261030/lower/radial_28_125_proposal.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print('weight rows',len(out['data']),'numerical objective gap',-s.fun,'group maxima',s.x[m:])
