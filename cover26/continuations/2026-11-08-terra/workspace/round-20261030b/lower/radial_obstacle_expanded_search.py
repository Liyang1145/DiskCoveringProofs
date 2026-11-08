import numpy as np,json
from pathlib import Path
from scipy.optimize import milp,Bounds,LinearConstraint
from fractions import Fraction as F
r=F(9,40);rf=float(r);t=[F(x) for x in ('23/100','19/75','83/300','3/10','97/300','26/75','37/100','59/100','37/60','193/300','67/100','209/300','217/300','3/4','1','11/20','23/40','47/80','3/5','49/80','5/8')]
ds=[F(i,1000) for i in range(1,1001)]+[F(0),r,1-r];ds=sorted(set(ds));v=np.array(list(map(float,ds)));A=np.zeros((len(t),len(ds)))
for j,tf in enumerate(t):
 x=float(tf);mask=(abs(v-x)<rf)&(v>0);A[j,mask]=np.arccos(np.clip((x*x+v[mask]**2-rf*rf)/(2*x*v[mask]),-1,1))
for B in (16,):
 # maximize uniform excess epsilon for the finite list of angular inequalities
 caps=[(.452,3),(.485,4),(.545,5),(.61,6),(.676,8),(.737,9),(.77,10),(.795,11)]
 thresholds=[.8,.8125,.825,.8375,.85,.875]
 mins=[13,13,12,11,10,6] if B==15 else [12,11,10,8,6,0]
 tvals=[.55,.575,.5875,.6,.6125,.625]
 inner=[8,8,8,7,6,6] if B==15 else [8,7,6,5,4,2]
 extra=[(v<=rf,1)]+[(v<=cap,k) for cap,k in caps]+[(v>z,k) for z,k in zip(thresholds,mins)]+[((v>z-rf)&(v<1-rf),k) for z,k in zip(tvals,inner)]
 AA=np.zeros((len(t)+2+len(extra),len(ds)+1));AA[:len(t),:-1]=A;AA[:len(t),-1]=-1
 AA[len(t),:-1]=1;AA[len(t)+1,:-1]=(v>=1-rf)
 for j,(mask,k) in enumerate(extra):AA[len(t)+2+j,:-1]=mask
 lb=np.r_[np.full(len(t),np.pi),26,B,[k for mask,k in extra]]
 ub=np.r_[np.full(len(t),np.inf),26,B,np.full(len(extra),np.inf)]
 s=milp(np.r_[np.zeros(len(ds)),-1],integrality=np.r_[np.ones(len(ds)),0],bounds=Bounds(np.zeros(len(ds)+1),np.r_[np.full(len(ds),26),2]),constraints=LinearConstraint(AA,lb,ub),options={'time_limit':40,'mip_rel_gap':0.1})
 print(B,'status',s.status,'slack',None if s.x is None else s.x[-1],flush=True)
 if s.x is not None:
  out={'r':str(r),'B':B,'circles':[str(z) for z in t],'radii_counts':[[str(d),int(round(k))] for d,k in zip(ds,s.x[:-1]) if k>.5],'interpretation':'Radial angle capacity relaxation only; not a geometric configuration.'}
  Path(f'round-20261030b/lower/radial_relax_expanded_B{B}.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
