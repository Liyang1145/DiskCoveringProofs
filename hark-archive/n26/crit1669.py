"""Diagnostic (float): second-order sufficient condition at theta*: is H0 (Hessian of Phi_lam0) PD on the critical cone?"""
import numpy as np, json, itertools, mpmath as mp
import kkt2 as K2
from scipy.linalg import null_space
from scipy.optimize import linprog
S=np.load('struct1669.npz'); AX=S['AX']; BT=S['BT']; lam0=S['lam0']; th=S['th']
D=json.load(open('kkt2_122.json')); A=D['A']
Z=[k for k in range(len(A)) if lam0[k]<1e-12]
print('zero rods',[A[k] for k in Z])
E=K2.E
# witness triples among zero rods
from collections import defaultdict
byv=defaultdict(list)
for k in Z:
    u,v=E[A[k]]; byv[max(u,v)].append(A[k])
print('zero rods grouped by higher endpoint',dict(byv))
Na=null_space(AX)
# cone {nu in null: nu_Z>=0}: param nu=Na c ; constraints Na[Z] c >=0
NZ=Na[Z]; print('rank Na[Z]',np.linalg.matrix_rank(NZ,1e-9),'shape',NZ.shape)
# extreme rays: assume simplicial: solve for c with NZ c = e_T patterns -> use per-group
# H0
w=np.zeros(134); w[A]=lam0
def schur(w):
    L=np.zeros((76,76))
    for (u,v),x in zip(E,w): L[u,u]+=x;L[v,v]+=x;L[u,v]-=x;L[v,u]-=x
    keep=[i for i in range(16,76) if L[i,i]>1e-300]
    return -(L[:16,:16]-L[:16,keep]@np.linalg.solve(L[np.ix_(keep,keep)],L[keep,:16]))
from hess_probe import phi_g_H
phi,g,H0=phi_g_H(schur(w),th); print('phi/W',phi/w.sum(),'|g|',np.abs(g).max(),'eig H0',np.linalg.eigvalsh(H0)[:4])
np.save('H0.npy',H0)
# rays of K: generators g = BT Na c for c in cone NZ c>=0 . compute via LP: min u^T H0 u over C approx by random projected sampling + local opt
Gc=BT@Na   # 15 x 11 ; K = {Gc c : NZ c >= 0}
# C = {u: (Gc c).u <=0 for all c with NZ c>=0}  <=> Gc^T u in -(cone NZ^T ...)  ; check via LP per u
def inC(u):
    # max (Gc^T u).c s.t. NZ c >= 0, |c|_inf<=1  ; u in C iff max <= 0
    r=linprog(-(Gc.T@u),A_ub=-NZ,b_ub=np.zeros(len(Z)),bounds=[(-1,1)]*Na.shape[1],method='highs'); return -r.fun
rng=np.random.default_rng(0); best=1e9; cnt=0
ev,V=np.linalg.eigh(H0)
for v in V.T[:3]:
    print('eigvec %.4f'%(v@H0@v),'phi1(v)=%.3e'%inC(v),'phi1(-v)=%.3e'%inC(-v))
for trial in range(3000):
    u=rng.standard_normal(15); u/=np.linalg.norm(u)
    if inC(u)<=1e-12:
        cnt+=1; q=u@H0@u; best=min(best,q)
print('random dirs in C',cnt,'/3000, min uHu',best)
