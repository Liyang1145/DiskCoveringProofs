"""Numerical exploratory LP only; never an exact certificate."""
import numpy as np
from scipy.optimize import linprog
r=.4425
t=np.linspace(.02,1,100)
d=np.linspace(0,1+r,900)
T=t[None,:]; D=d[:,None]
with np.errstate(divide='ignore',invalid='ignore'):
    c=(T*T+D*D-r*r)/(2*T*D)
    a=np.where(D+T<=r,np.pi,np.where(np.abs(T-D)>=r,0,np.arccos(np.clip(c,-1,1))))
    a[0]=np.where(t<=r,np.pi,0)
bound=a[d>=1-r]; center=a[d<=r]
Ab=np.concatenate([np.column_stack([bound,-np.ones(len(bound)),np.zeros(len(bound))]),np.column_stack([center,np.zeros(len(center)),-np.ones(len(center))])])
res=linprog(np.r_[np.zeros(len(t)),7.,1.],A_ub=Ab,b_ub=np.zeros(len(Ab)),A_eq=[np.r_[np.ones(len(t)),0,0]],b_eq=[1],bounds=[(0,None)]*(len(t)+2),method='highs')
print('numerical sampled lower bound on relaxation objective:',res.fun,'pi:',np.pi,'status:',res.message)
print('nonzero terms:',[(round(t[i],4),round(v,6)) for i,v in enumerate(res.x[:-2]) if v>1e-6])
