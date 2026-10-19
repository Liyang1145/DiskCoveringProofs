"""Float proposer: robust weights w maximizing min_{theta in box} Phi_w(theta)/W - R*^2
(Kelley/level bundle on the concave function). Floats only propose; verdict is rigorous elsewhere."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import numpy as np, cvxpy as cp, json
from scipy.optimize import minimize
M=json.load(open(DCP_N26+'/model134.json')); E=[tuple(e) for e in M['edges']]
U=np.array([e[0] for e in E]); V=np.array([e[1] for e in E])
RS2=0.234700090400448239616790133776692127560495963654971391785925**2
IU,JU=np.triu_indices(16,1)
def schur(w):
    L=np.zeros((76,76)); np.add.at(L,(U,U),w); np.add.at(L,(V,V),w); np.add.at(L,(U,V),-w); np.add.at(L,(V,U),-w)
    Xh=np.linalg.solve(L[16:,16:],-L[16:,:16])   # harmonic map anchors->free
    S=L[:16,:16]+L[:16,16:]@Xh
    return -S[IU,JU], Xh
def phi_and_grad(th,C):
    t=np.concatenate([[0],th]); d=2*np.pi*(t[JU]-t[IU])
    f=np.sum(2*C*(1-np.cos(d))); gd=4*np.pi*C*np.sin(d)
    g=np.zeros(16); np.add.at(g,JU,gd); np.add.at(g,IU,-gd); return f,g[1:]
def inner_min(C,lo,hi,starts,hp=False):
    best=None
    for x0 in starts:
        r=minimize(phi_and_grad,np.clip(x0,lo,hi),args=(C,),jac=True,bounds=list(zip(lo,hi)),method='L-BFGS-B',options=({'maxiter':1000,'ftol':1e-16,'gtol':1e-14} if hp else {'maxiter':200}))
        if best is None or r.fun<best[0]: best=(r.fun,r.x)
    return best
def D_of(th,Xh):
    t=np.concatenate([[0],th]); A=np.stack([np.cos(2*np.pi*t),np.sin(2*np.pi*t)],1)
    P=np.vstack([A,Xh@A]); Dv=P[U]-P[V]; return (Dv*Dv).sum(1)
KW={}
def robust_weights(lo,hi,w0,iters=40,rng=None,verbose=False,target=None,callback=None,every=25,giveup=None,floor=1e-7,tol=1e-7,sc=1.0,hp=False):
    global KW
    KW=dict(tol_gap_abs=1e-12,tol_gap_rel=1e-12,tol_feas=1e-12) if hp else {}
    rng=rng or np.random.default_rng(0)
    w=np.maximum(w0,floor); w/=w.sum()
    cuts=[]; pts=[ (lo+hi)/2 ]+[lo+(hi-lo)*rng.random(len(lo)) for _ in range(4)]
    bestw,bestv=None,-1e9; level_lb=None
    for it in range(iters):
        C,Xh=schur(w); f,th=inner_min(C,lo,hi,pts[-8:],hp)
        v=f/w.sum()-RS2
        if v>bestv: bestv,bestw=v,w.copy()
        if verbose: print(it,'%.3e'%v,'best %.3e'%bestv)
        if target is not None and bestv>target: break
        if callback is not None and it%every==every-1 and bestv>0:
            if callback(bestw): return bestw,bestv,True
        if giveup is not None and it>=giveup[0] and bestv<giveup[1]: break
        pts.append(th); cuts.append(D_of(th,Xh))
        # level method: project current best onto level set {t_model >= level}
        Dm=np.array(cuts)
        x=cp.Variable(134); tt=cp.Variable()
        Ds=(Dm-RS2)*sc
        ub=cp.Problem(cp.Maximize(tt),[tt<=Ds@x,cp.sum(x)==1,x>=floor]); ub.solve(solver='CLARABEL',**KW)
        ubv=ub.value/sc
        if ubv-bestv<tol: break
        lev=bestv+0.3*(ubv-bestv)
        pr=cp.Problem(cp.Minimize(cp.sum_squares(x-bestw)),[Ds@x>=lev*sc,cp.sum(x)==1,x>=floor]); pr.solve(solver='CLARABEL',**KW)
        w=np.maximum(x.value,floor); w/=w.sum()
    if callback is not None:
        return bestw,bestv,(bestv>0 and callback(bestw))
    return bestw,bestv
if __name__=='__main__':
    import sys,time
    from fractions import Fraction as F
    import bnb, certify_box as cb
    idx=int(sys.argv[1]); b=bnb.BOX[idx]
    lo=np.array([float(F(x)) for x in b['lower']]); hi=np.array([float(F(x)) for x in b['upper']])
    lam,_=cb.fit_weights(np.array(bnb.DIAG[idx]['None'][1]))
    t=time.time(); w,v=robust_weights(lo,hi,lam,iters=int(sys.argv[2]),verbose=True); print('time',time.time()-t,'robust',v, 'model min margin', bnb.DIAG[idx]['None'][0]**2-RS2)
