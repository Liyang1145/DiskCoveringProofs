"""PROPOSAL ONLY (no verdict): high-precision KKT point of the joint minimax
min_{theta,X} max_{e in A} |p_u-p_v|^2 with active set A, dead free vertices removed."""
import json, numpy as np, mpmath as mp, sys, os
import kkt1669 as K
from scipy.optimize import nnls
E=K.E
z0=np.load('slsqp_z.npy'); P0=K.pos(z0); sl=z0[135]**2-((P0[K.U]-P0[K.V])**2).sum(1)
ATH=float(os.environ.get('ATH','1e-7'))
A=[i for i in range(134) if sl[i]<ATH]
if os.environ.get('DROP'): A=[i for i in A if i not in json.loads(os.environ['DROP'])]
nA=len(A)
deg=np.zeros(76,int)
for i in A: u,v=E[i]; deg[u]+=1; deg[v]+=1
live=[i for i in range(16,76) if deg[i]>0]; idx={v:k for k,v in enumerate(live)}; nX=2*len(live)
N=15+nX+nA+1
def F(z, lib=np):
    if lib is np: cos,sin,pi=np.cos,np.sin,np.pi
    else: cos,sin,pi=mp.cos,mp.sin,mp.pi
    th=[0]+list(z[:15]); X=z[15:15+nX]; lam=z[15+nX:15+nX+nA]; s=z[-1]
    def P(w): return (cos(2*pi*th[w]),sin(2*pi*th[w])) if w<16 else (X[2*idx[w]],X[2*idx[w]+1])
    dP=[(-2*pi*sin(2*pi*t),2*pi*cos(2*pi*t)) for t in th]
    r1=[];gX=[[0,0] for _ in live];gT=[0]*16
    for e,l in zip(A,lam):
        u,v=E[e]; pu=P(u); pv=P(v); dx=pu[0]-pv[0]; dy=pu[1]-pv[1]
        r1.append(dx*dx+dy*dy-s)
        for w,sg in ((u,1),(v,-1)):
            if w>=16: gX[idx[w]][0]+=2*l*sg*dx; gX[idx[w]][1]+=2*l*sg*dy
            else: gT[w]+=2*l*sg*(dx*dP[w][0]+dy*dP[w][1])
    return r1+[g for xy in gX for g in xy]+gT[1:]+[sum(lam)-1]
def J(z,h=1e-7):
    Jm=np.empty((N,N))
    for k in range(N):
        zp=z.copy(); zp[k]+=h; zm=z.copy(); zm[k]-=h
        Jm[:,k]=(np.array(F(zp))-np.array(F(zm)))/(2*h)
    return Jm
def positions(th,X):
    t=[0]+list(th); out=[]
    for w in range(76):
        if w<16: out.append((mp.cos(2*mp.pi*t[w]),mp.sin(2*mp.pi*t[w])))
        elif w in idx: out.append((X[2*idx[w]],X[2*idx[w]+1]))
        else: out.append(None)
    return out
if __name__=='__main__':
    Xl=np.concatenate([P0[w] for w in live])
    z=np.concatenate([z0[:15],Xl,np.ones(nA)/nA,[z0[135]**2]])
    Jm=J(z); f=np.array(F(z)); cols=list(range(15+nX,15+nX+nA)); rows=list(range(nA,N-1))
    Ar=Jm[np.ix_(rows,cols)]; b=-(f[rows]-Ar@z[cols]); lam0,_=nnls(Ar,b); z[cols]=lam0/lam0.sum()
    for it in range(10):
        f=np.array(F(z)); Jm=J(z); z=z+np.linalg.solve(Jm,-f)
    print('nA',nA,'float |F|',np.abs(np.array(F(z))).max(),'cond %.1e'%np.linalg.cond(Jm),flush=True)
    mp.mp.dps=int(os.environ.get('DPS','60')); Ji=np.linalg.inv(J(z))
    zm=[mp.mpf(float(x)) for x in z]
    for it in range(40):
        f=F(zm,mp); nf=max(abs(x) for x in f)
        if nf<mp.mpf(10)**(-mp.mp.dps+8): break
        # residual in mp, correction via float inverse applied to scaled residual
        sc=float(nf); d=Ji@(np.array([float(x/nf) for x in f])); zm=[a-mp.mpf(float(b))*nf for a,b in zip(zm,d)]
    print('mp |F|',mp.nstr(nf,5),'iters',it)
    lam=zm[15+nX:15+nX+nA]; s=zm[-1]
    print('min lam',mp.nstr(min(lam),8),'sqrt s',mp.nstr(mp.sqrt(s),45))
    Pm=positions(zm[:15],zm[15:15+nX])
    # inactive slacks: inactive rod with a dead endpoint -> place dead vertex optimally later; report rods with both ends live
    sls=[]
    for e in range(134):
        if e in A: continue
        u,v=E[e]
        if Pm[u] is None or Pm[v] is None: sls.append((e,'dead-endpoint')); continue
        d2=(Pm[u][0]-Pm[v][0])**2+(Pm[u][1]-Pm[v][1])**2; sls.append((e,mp.nstr(s-d2,6)))
    print('inactive slacks',sls)
    t=[mp.mpf(0)]+zm[:15]; print('D2 dev',mp.nstr(max(abs(t[k+8]-t[k]-mp.mpf(1)/2) for k in range(8)),5),'theta8-1/2',mp.nstr(t[8]-mp.mpf(1)/2,8))
    json.dump({'A':A,'live':live,'z':[mp.nstr(x,mp.mp.dps-2) for x in zm]},open('kkt2_%d.json'%nA,'w'))
