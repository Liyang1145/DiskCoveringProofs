"""Float PROPOSAL: joint second-order model of Psi(theta,w)=Phi_w(theta)-W R*^2 at (theta*,lam0).
dPsi/dw_e = |e(X*)|^2 - R*^2.  G = d2Psi/dw dtheta, D = -d2Psi/dw2 (on positive-multiplier rods P).
sup_tau of 2nd-order model = 1/2 u^T (H0 + G^T D^+ G) u."""
import numpy as np, json, hp
E=hp.E; U=np.array([e[0] for e in E]); V=np.array([e[1] for e in E])
lam0=np.array([float(x) for x in hp.LAM0]); th0=np.array([float(x) for x in hp.THSTAR])
P=[e for e in range(134) if lam0[e]>0]
R2=float(hp.RUP2)
def lens(w,th):
    use=w>0; fv=sorted({v for k in np.nonzero(use)[0] for v in E[k] if v>=16}); ix={v:i for i,v in enumerate(fv)}
    L=np.zeros((76,76))
    for k in np.nonzero(use)[0]:
        u,v=E[k];x=w[k];L[u,u]+=x;L[v,v]+=x;L[u,v]-=x;L[v,u]-=x
    t=np.concatenate([[0],th]); Aa=np.stack([np.cos(2*np.pi*t),np.sin(2*np.pi*t)],1)
    Pp=np.full((76,2),np.nan); Pp[:16]=Aa
    Pp[fv]=-np.linalg.solve(L[np.ix_(fv,fv)],L[np.ix_(fv,list(range(16)))]@Aa)
    d=Pp[U]-Pp[V]; return (d*d).sum(1)
if __name__=='__main__':
    l0=lens(lam0,th0); print('active len dev',np.abs(l0[P]-R2).max())
    h=1e-6; G=np.zeros((len(P),15))
    for i in range(15):
        e=np.zeros(15); e[i]=h; G[:,i]=(lens(lam0,th0+e)[P]-lens(lam0,th0-e)[P])/(2*h)
    D=np.zeros((len(P),len(P))); hw=1e-7
    for a,ea in enumerate(P):
        w1=lam0.copy(); w1[ea]+=hw; w2=lam0.copy(); w2[ea]-=hw
        D[:,a]=-(lens(w1,th0)[P]-lens(w2,th0)[P])/(2*hw)
    D=(D+D.T)/2; H0=np.load('H0_hp.npy')
    ev=np.linalg.eigvalsh(D); print('D eig min/max',ev[:3],ev[-1])
    Dp=np.linalg.pinv(D,rcond=1e-10); M=H0+G.T@Dp@G
    print('eig M',np.linalg.eigvalsh(M)[:5])
    np.savez('homog2.npz',G=G,D=D,P=np.array(P),M=M)
