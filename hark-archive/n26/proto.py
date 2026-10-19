import json,numpy as np, cvxpy as cp
from fractions import Fraction as F
import certify_box as cb, bnb
RS2=float(cb.RUP2)
def comps(pairs,W,lo,hi,mode):
    lo=np.array([0.]+[float(x) for x in lo]); hi=np.array([0.]+[float(x) for x in hi])
    m=(lo+hi)/2; r=(hi-lo)/2
    phi=0; g=np.zeros(16); H=np.zeros((16,16)); cub=0
    for (i,j),c in pairs.items():
        c=float(c); d=m[j]-m[i]; s=r[i]+r[j]
        phi+=2*c*(1-np.cos(2*np.pi*d)); gd=4*np.pi*c*np.sin(2*np.pi*d); g[j]+=gd; g[i]-=gd
        h=8*np.pi**2*c*np.cos(2*np.pi*d)
        M3=16*np.pi**3*c*min(1,abs(np.sin(2*np.pi*d))+2*np.pi*s)
        if mode=='v2': h-= M3*s/3   # f>=f0+f1 t+1/2(f2 - M3 s/3) t^2
        H[i,i]+=h;H[j,j]+=h;H[i,j]-=h;H[j,i]-=h
        if mode=='v1': cub+=(8/3)*np.pi**3*c*s**3
    g=g[1:];H=H[1:,1:];r=r[1:]
    lm=np.linalg.eigvalsh(H).min()
    sh=min(0,lm-1e-12)
    Hs=H-sh*np.eye(15)
    d=cp.Variable(15); pr=cp.Problem(cp.Minimize(g@d+0.5*cp.quad_form(d,cp.psd_wrap(Hs))),[cp.abs(d)<=r]); pr.solve(solver='CLARABEL')
    q=pr.value + sh/2*(r**2).sum()
    return dict(gap=(phi-W*RS2)/W, qp=q/W, cub=cub/W, shiftpen=sh/2*(r**2).sum()/W, total=(phi-W*RS2+q-cub)/W, lmin=lm/W)
if __name__=='__main__':
    import sys
    idx=int(sys.argv[1])
    b=bnb.BOX[idx]; lo=[F(x) for x in b['lower']]; hi=[F(x) for x in b['upper']]
    th=np.array(bnb.DIAG[idx]['None'][1]); lam,s=cb.fit_weights(th)
    pairs,W=cb.exact_pairs(cb.rationalize_weights(lam)); W=float(W)
    for mode in ['v1','v2']: print(mode,{k:'%.2e'%v for k,v in comps(pairs,W,lo,hi,mode).items()})
