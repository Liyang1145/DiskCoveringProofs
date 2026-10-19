"""PROPOSAL/diagnostic: local structure of the model minimax at theta* (from kkt2_122.json)."""
import json, numpy as np, mpmath as mp
import kkt2 as K2
from scipy.linalg import null_space
from scipy.optimize import linprog
D=json.load(open('kkt2_122.json')); A=D['A']; live=D['live']; z=np.array([float(mp.mpf(x)) for x in D['z']])
nX=2*len(live); nA=len(A); th=z[:15]; X=z[15:15+nX]; lam0=z[15+nX:15+nX+nA]
idx={v:k for k,v in enumerate(live)}
t=np.concatenate([[0],th])
def P(w): return np.array([np.cos(2*np.pi*t[w]),np.sin(2*np.pi*t[w])]) if w<16 else X[2*idx[w]:2*idx[w]+2]
AX=np.zeros((nX,nA)); BT=np.zeros((15,nA))
for k,e in enumerate(A):
    u,v=K2.E[e]; d=P(u)-P(v)
    for w,sg in ((u,1),(v,-1)):
        if w>=16: AX[2*idx[w]:2*idx[w]+2,k]+=2*sg*d
        elif w>0: BT[w-1,k]+=2*sg*(d@np.array([-2*np.pi*np.sin(2*np.pi*t[w]),2*np.pi*np.cos(2*np.pi*t[w])]))
Na=null_space(AX); print('dim null(AX) (incl. normalisation dir)',Na.shape[1])
GS=BT@Na; sv=np.linalg.svd(GS,compute_uv=False); print('sv of B*null',sv)
print('lam0 zero comps',[A[k] for k in range(nA) if lam0[k]<1e-12],'B lam0',np.abs(BT@lam0).max(),'AX lam0',np.abs(AX@lam0).max())
np.savez('struct1669.npz',AX=AX,BT=BT,Na=Na,lam0=lam0,th=th)
