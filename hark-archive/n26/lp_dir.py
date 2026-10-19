import numpy as np, json
from scipy.optimize import linprog
S=np.load('struct1669.npz'); AX=S['AX']; BT=S['BT']; nX,nA=AX.shape
# box-relative bounds for u in units of delta=2.9451e-10
dl=2.9451e-10
lo_rel=[2.8109e-10,4.0784e-10,5.0042e-10,2.6927e-11,3.5234e-10,4.7909e-10]; hi_rel=[4.174e-10,2.9066e-10,1.9807e-10,6.7157e-10,3.4615e-10,2.1941e-10]
for BIG in (1e1,1e3,1e5):
    bnds=[(-l/dl,h/dl) for l,h in zip(lo_rel,hi_rel)]+[(-BIG,-1),(-BIG,-1)]+[(-BIG,BIG)]*6+[(0,BIG)]+[(-BIG*10,BIG*10)]*nX+[(None,None)]
    # vars: u(15), dX(nX), t ; minimize t ; b_e.u + a_e.dX - t <= 0
    Aub=np.hstack([BT.T,AX.T,-np.ones((nA,1))]); c=np.zeros(15+nX+1); c[-1]=1
    r=linprog(c,A_ub=Aub,b_ub=np.zeros(nA),bounds=bnds,method='highs')
    print(BIG,r.status,'min directional growth (r^2 per delta)',r.fun,'u',np.round(r.x[:15],3))
