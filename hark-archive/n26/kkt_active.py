"""PROPOSAL ONLY: Newton on the KKT system with active set A (rods tight at SLSQP opt).
Unknowns (theta15, X120, lam_A, s)."""
import json, numpy as np, mpmath as mp, sys
import kkt1669 as K
M=json.load(open('model134.json')); E=[tuple(e) for e in M['edges']]
z0=np.load('slsqp_z.npy'); P0=K.pos(z0); sl=z0[135]**2-((P0[K.U]-P0[K.V])**2).sum(1)
TH=float(__import__("os").environ.get("ATH","1e-7")); A=[i for i in range(134) if sl[i]<TH]; nA=len(A); N=135+nA+1
def F(z, lib=np):
    if lib is np: cos,sin,pi=np.cos,np.sin,np.pi
    else: cos,sin,pi=mp.cos,mp.sin,mp.pi
    th=[0]+list(z[:15]); X=z[15:135]; lam=z[135:135+nA]; s=z[135+nA]
    P=[(cos(2*pi*t),sin(2*pi*t)) for t in th]+[(X[2*i],X[2*i+1]) for i in range(60)]
    dP=[(-2*pi*sin(2*pi*t),2*pi*cos(2*pi*t)) for t in th]
    r1=[];gX=[[0,0] for _ in range(60)];gT=[0]*16
    for idx,l in zip(A,lam):
        u,v=E[idx]; dx=P[u][0]-P[v][0]; dy=P[u][1]-P[v][1]
        r1.append(dx*dx+dy*dy-s)
        for w,sg in ((u,1),(v,-1)):
            if w>=16: gX[w-16][0]+=2*l*sg*dx; gX[w-16][1]+=2*l*sg*dy
            else: gT[w]+=2*l*sg*(dx*dP[w][0]+dy*dP[w][1])
    return r1+[g for xy in gX for g in xy]+gT[1:]+[sum(lam)-1]
def J(z,h=1e-7):
    Jm=np.empty((N,N))
    for k in range(N):
        zp=z.copy(); zp[k]+=h; zm=z.copy(); zm[k]-=h
        Jm[:,k]=(np.array(F(zp))-np.array(F(zm)))/(2*h)
    return Jm
if __name__=='__main__':
    # initial lam: least squares on stationarity rows
    z=np.concatenate([z0[:135],np.ones(nA)/nA,[z0[135]**2]])
    Jm=J(z); rows=list(range(nA,N)); cols=list(range(135,135+nA))
    f=np.array(F(z)); 
    # stationarity is linear in lam: solve Jm[rows][:,cols] lam = -(f_rows - Jm[rows][:,cols] lam0)
    Ar=Jm[np.ix_(rows,cols)]; b=-(f[rows]-Ar@z[cols]); lam0=np.linalg.lstsq(Ar,b,rcond=None)[0]; z[cols]=lam0
    print('nA',nA,'init lam min',lam0.min(),flush=True)
    for it in range(8):
        f=np.array(F(z)); Jm=J(z); dz=np.linalg.solve(Jm,-f); z=z+dz
        print(it,'|F|',np.abs(f).max(),'cond %.2e'%np.linalg.cond(Jm),'minlam',z[135:135+nA].min(),flush=True)
    np.save('kkt_active_z.npy',z); json.dump(A,open('kkt_active_A.json','w'))
    # high precision refinement with float Jacobian
    mp.mp.dps=60; Jinv=np.linalg.inv(Jm)
    zm=[mp.mpf(float(x)) for x in z]
    for it in range(8):
        f=F(zm,mp); nf=max(abs(x) for x in f)
        d=Jinv@np.array([float(x) for x in f]); zm=[a-mp.mpf(float(b)) for a,b in zip(zm,d)]
        print('mp',it,mp.nstr(nf,5),flush=True)
        # note: float correction only reaches ~1e-16 relative; use mp residual w/ float J (iterative refinement)
    json.dump([mp.nstr(x,55) for x in zm],open('kkt_active_mp.json','w'))
    t=[0]+[float(x) for x in zm[:15]]; print('D2 dev',max(abs(t[k+8]-t[k]-0.5) for k in range(8)),'sqrt s',mp.nstr(mp.sqrt(zm[135+nA]),40))
    others=[i for i in range(134) if i not in A]
    P=K.pos(z[:136]); l2=((P[K.U]-P[K.V])**2).sum(1); print('inactive slack min',(z[135+nA]-l2[others]).min())
