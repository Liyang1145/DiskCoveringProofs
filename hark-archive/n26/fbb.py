# float-only prototype B&B to compare heuristics (NOT a proof)
import json,numpy as np, cvxpy as cp, time, sys
from fractions import Fraction as F
import certify_box as cb, bnb
RS2=float(cb.RUP2)
def fbound(pairs,W,lo,hi):
    lo=np.concatenate([[0.],lo]); hi=np.concatenate([[0.],hi]); m=(lo+hi)/2; r=(hi-lo)/2
    phi=0; g=np.zeros(16); H=np.zeros((16,16)); cub=0
    for (i,j),c in pairs.items():
        d=m[j]-m[i]; s=r[i]+r[j]
        phi+=2*c*(1-np.cos(2*np.pi*d)); gd=4*np.pi*c*np.sin(2*np.pi*d); g[j]+=gd; g[i]-=gd
        h=8*np.pi**2*c*np.cos(2*np.pi*d); H[i,i]+=h;H[j,j]+=h;H[i,j]-=h;H[j,i]-=h
        cub+=(8/3)*np.pi**3*c*s**3
    g=g[1:];H=H[1:,1:];r=r[1:]
    lm=np.linalg.eigvalsh(H).min(); sh=min(0,lm-1e-12); Hs=H-sh*np.eye(15)
    d=cp.Variable(15); pr=cp.Problem(cp.Minimize(g@d+0.5*cp.quad_form(d,cp.psd_wrap(Hs))),[cp.abs(d)<=r]); pr.solve(solver='CLARABEL')
    return (phi-W*RS2+pr.value+sh/2*(r**2).sum()-cub)/W, g, H, r
def fw(th):
    lam,_=cb.fit_weights(th); w=np.maximum(lam,0)+1e-7
    # float Schur
    import numpy.linalg as la
    L=np.zeros((76,76))
    for (u,v),x in zip(cb.E,w): L[u,u]+=x;L[v,v]+=x;L[u,v]-=x;L[v,u]-=x
    S=L[:16,:16]-L[:16,16:]@la.solve(L[16:,16:],L[16:,:16])
    return {(i,j):-S[i,j] for i in range(16) for j in range(i+1,16) if -S[i,j]>1e-14}, w.sum()
def run(idx, split, refit, budget=400):
    b=bnb.BOX[idx]; lo0=np.array([float(F(x)) for x in b['lower']]); hi0=np.array([float(F(x)) for x in b['upper']])
    leaves=[0];nodes=[0];op=[0]
    pw=fw(np.array(bnb.DIAG[idx]['None'][1]))
    stack=[(lo0,hi0,pw,0)]
    while stack:
        lo,hi,pw,dep=stack.pop(); nodes[0]+=1
        if nodes[0]>budget: return 'budget',leaves[0],nodes[0]
        bd,g,H,r=fbound(*pw,lo,hi)
        if bd>0: leaves[0]+=1; continue
        if refit:
            wp=bnb.worst_point(lo,hi); pw2=fw(wp[1]); bd2,g,H,r=fbound(*pw2,lo,hi)
            if bd2>0: leaves[0]+=1; continue
            pw=pw2
        if split=='wide': ax=int(np.argmax(hi-lo))
        else: ax=int(np.argmax(np.abs(g)*r+0.5*np.abs(np.diag(H))*r*r))
        mid=(lo[ax]+hi[ax])/2; h1=hi.copy();h1[ax]=mid; l2=lo.copy(); l2[ax]=mid
        stack.append((lo,h1,pw,dep+1)); stack.append((l2,hi,pw,dep+1))
    return 'done',leaves[0],nodes[0]
if __name__=='__main__':
    idx=int(sys.argv[1]); sp=sys.argv[2]
    t=time.time(); print(idx,sp,run(idx,sp,True,int(sys.argv[3])), time.time()-t)
