"""Homogeneous second-order model at theta* (PROPOSAL data, not a verdict):
F(rho u, rho tau) / rho^2 -> f(u,tau) = tau.G u + 1/2 u^T H0 u - 1/2 tau^T D tau,
tau = extra weight on the 30 zero-multiplier active rods. Evaluated with arb at rho=1e-20."""
import numpy as np, json, hp
from fractions import Fraction as F
Z=[e for e in hp.ACT if hp.LAM0[e]==0]
assert len(Z)==30
rho=F(1,10**20)
def Fval(u,tau):
    w=list(hp.LAM0)
    for e,t in zip(Z,tau): w[e]+=rho*F(t)
    c,W=hp.pairs_arb(w)
    th=[a+rho*F(b) for a,b in zip(hp.THSTAR,u)]
    m=hp.phi_g_H(c,th)[0]-hp.A(W)*hp.A(hp.RUP2)
    return float((m/hp.A(rho*rho)).mid())
if __name__=='__main__':
    f0=Fval([0]*15,[0]*30)
    fu=[Fval([1 if k==i else 0 for k in range(15)],[0]*30) for i in range(15)]
    ft=[Fval([0]*15,[1 if k==i else 0 for k in range(30)]) for i in range(30)]
    G=np.zeros((30,15))
    for a in range(30):
        for i in range(15):
            G[a,i]=Fval([1 if k==i else 0 for k in range(15)],[1 if k==a else 0 for k in range(30)])-fu[i]-ft[a]+f0
    D=np.zeros((30,30))
    for a in range(30): D[a,a]=-2*ft[a]
    for a in range(30):
        for b in range(a+1,30):
            v=Fval([0]*15,[1 if k in(a,b) else 0 for k in range(30)])
            D[a,b]=D[b,a]=-(v-ft[a]-ft[b]+f0)
    np.savez('homog.npz',G=G,D=D,Z=np.array(Z),f0=f0)
    print('f0',f0,'G rank',np.linalg.matrix_rank(G,1e-8),'D eig',np.linalg.eigvalsh(D)[:3],np.linalg.eigvalsh(D)[-1])
