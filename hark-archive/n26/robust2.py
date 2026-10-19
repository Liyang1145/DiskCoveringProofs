"""Robust weights by an exact finite-sample master problem (floats only propose):
  max_w min_s Phi_w(theta_s)/W  ==  min_{mu in simplex, z} max_e sum_s |mu_s p_u^s - mu_s p_v^s|^2/mu_s
(perspective / quad-over-lin form, jointly convex; z^s = mu_s x^s).  Edge duals = w.
Worst point for w added by multistart L-BFGS (robust.inner_min, high precision)."""
import numpy as np, cvxpy as cp
import robust as rb
E=rb.E; RS2=rb.RS2
def anchors(th):
    t=np.concatenate([[0],th]); return np.stack([np.cos(2*np.pi*t),np.sin(2*np.pi*t)],1)
def master(TH):
    S=len(TH); mu=cp.Variable(S,nonneg=True); Z=[cp.Variable((60,2)) for _ in range(S)]; t=cp.Variable()
    A=[anchors(th) for th in TH]; cons=[cp.sum(mu)==1]; ec=[]
    for (u,v) in E:
        terms=[]
        for s in range(S):
            pu=mu[s]*A[s][u] if u<16 else Z[s][u-16]
            pv=mu[s]*A[s][v] if v<16 else Z[s][v-16]
            terms.append(cp.quad_over_lin(pu-pv,mu[s]))
        c=cp.sum(terms)<=t; ec.append(c)
    pr=cp.Problem(cp.Minimize(t),cons+ec)
    pr.solve(solver='CLARABEL',tol_gap_abs=1e-13,tol_gap_rel=1e-13,tol_feas=1e-13,max_iter=400)
    w=np.array([max(float(np.ravel(c.dual_value)[0]),0.0) for c in ec]); return w/w.sum(), float(t.value)-RS2, mu.value
def robust2(lo,hi,w0,iters=30,callback=None,floor=1e-11,rng=None,verbose=False):
    rng=rng or np.random.default_rng(0)
    w=np.maximum(w0,floor); w/=w.sum()
    pts=[(lo+hi)/2]+[lo+(hi-lo)*rng.random(len(lo)) for _ in range(3)]
    TH=[]; bestw,bestv=None,-1e9; ub=None
    for it in range(iters):
        C,Xh=rb.schur(w); f,th=rb.inner_min(C,lo,hi,pts[-6:]+[ (lo+hi)/2 ],True)
        v=f/w.sum()-RS2
        if v>bestv: bestv,bestw=v,w.copy()
        if verbose: print(it,'v=%.4e best=%.4e master=%s'%(v,bestv,ub),flush=True)
        if bestv>0 and callback is not None and callback(bestw): return bestw,bestv,True
        if ub is not None and ub<=0: break           # sample set already infeasible: split
        TH.append(th); pts.append(th)
        try: w,ub,_=master(TH)
        except Exception as e:
            if verbose: print('master fail',e); break
        w=np.maximum(w,floor); w/=w.sum()
    return bestw,bestv,False
if __name__=='__main__':
    import sys
    from fractions import Fraction as F
    import shells1669 as S, certify_box as cb, bnb1669 as B
    t,sl=S.skeleton(); n=int(sys.argv[1]); lo,hi,j=sl[n]
    lof=np.array([float(x) for x in lo]); hif=np.array([float(x) for x in hi])
    lam,_=cb.fit_weights(B.TH)
    def cbk(w):
        p,W=cb.exact_pairs([F(x,10**15) for x in [int(y*10**15) for y in cb.rationalize_weights(w,floor=1e-11,den=10**15)]]); bd,_=cb.box_bound(p,W,lo,hi)
        print(' rig',float(bd/W)); return bd>0
    print(robust2(lof,hif,lam,iters=int(sys.argv[2]),callback=cbk,verbose=True)[1:])

# ---- well-conditioned exact reformulation around reference positions P* ----
def ref_positions(theta):
    A=anchors(theta); X=cp.Variable((60,2)); s=cp.Variable(); cons=[]
    for (u,v) in E:
        pu=A[u] if u<16 else X[u-16]; pv=A[v] if v<16 else X[v-16]
        cons.append(cp.sum_squares(pu-pv)<=s)
    cp.Problem(cp.Minimize(s),cons).solve(solver='CLARABEL')
    return np.vstack([A,X.value])
def master_local(TH,Pst,sig):
    """same optimum as master(); variables are scaled displacements from P*.
    sum_s |mu_s p_u^s - mu_s p_v^s|^2/mu_s - R*^2
      = c_e + 2 d*_e . sum_s dz^s_e + sum_s |dz^s_e|^2/mu_s,  z^s = mu_s (p^s - P*), sum mu = 1."""
    S=len(TH); mu=cp.Variable(S,nonneg=True); Zt=[cp.Variable((60,2)) for _ in range(S)]; tt=cp.Variable()
    Al=[(anchors(th)-Pst[:16])/sig for th in TH]   # scaled anchor displacements
    cons=[cp.sum(mu)==1]; ec=[]
    for (u,v) in E:
        d=Pst[u]-Pst[v]; ce=(d@d-RS2)/sig
        lin=0; quad=[]
        for s in range(S):
            zu=mu[s]*Al[s][u] if u<16 else Zt[s][u-16]
            zv=mu[s]*Al[s][v] if v<16 else Zt[s][v-16]
            dz=zu-zv; lin=lin+2*(d@dz); quad.append(cp.quad_over_lin(dz,mu[s]))
        c=ce+lin+sig*cp.sum(quad)<=tt; ec.append(c)
    pr=cp.Problem(cp.Minimize(tt),cons+ec); pr.solve(solver='CLARABEL',max_iter=400)
    w=np.array([max(float(np.ravel(c.dual_value)[0]),0.0) for c in ec]); return w/w.sum(), float(tt.value)*sig, mu.value
def robust3(lo,hi,w0,Pst,iters=30,callback=None,floor=1e-11,rng=None,verbose=False):
    rng=rng or np.random.default_rng(0)
    sig=max(float(np.max(hi-lo)),1e-12)
    w=np.maximum(w0,floor); w/=w.sum()
    pts=[(lo+hi)/2]+[lo+(hi-lo)*rng.random(len(lo)) for _ in range(3)]
    TH=[]; bestw,bestv=None,-1e9; ub=None
    for it in range(iters):
        C,Xh=rb.schur(w); f,th=rb.inner_min(C,lo,hi,pts[-6:]+[(lo+hi)/2],True)
        v=f/w.sum()-RS2
        if v>bestv: bestv,bestw=v,w.copy()
        if verbose: print(it,'v=%.4e best=%.4e master=%s'%(v,bestv,ub),flush=True)
        if bestv>0 and callback is not None and callback(bestw): return bestw,bestv,True
        if ub is not None and ub<=0: break
        TH.append(th); pts.append(th)
        try: w,ub,_=master_local(TH,Pst,sig)
        except Exception as e:
            if verbose: print('master fail',e); break
        w=np.maximum(w,floor); w/=w.sum()
    return bestw,bestv,False
