import numpy as np, json, cvxpy as cp
import kkt1669 as K
E=K.E
z=np.load('slsqp_z.npy'); th=z[:15]; t=np.concatenate([[0],th])
a=np.array([(t[k]+t[k+8]-0.5)/2 for k in range(8)]); a[0]=0
ts=np.concatenate([a,a+0.5]); th2=ts[1:]
def fitw(th,tol=1e-12):
    tt=np.concatenate([[0.0],th]); A=np.stack([np.cos(2*np.pi*tt),np.sin(2*np.pi*tt)],1)
    X=cp.Variable((60,2)); s=cp.Variable(); cons=[]
    for (u,v) in E:
        pu=A[u] if u<16 else X[u-16]; pv=A[v] if v<16 else X[v-16]
        cons.append(cp.sum_squares(pu-pv)<=s)
    cp.Problem(cp.Minimize(s),cons).solve(solver='CLARABEL',tol_gap_abs=tol,tol_gap_rel=tol,tol_feas=tol,max_iter=500)
    lam=np.array([max(float(np.ravel(c.dual_value)[0]),0) for c in cons]); return lam/lam.sum(), float(s.value)
def schur(w):
    L=np.zeros((76,76))
    for (u,v),x in zip(E,w): L[u,u]+=x;L[v,v]+=x;L[u,v]-=x;L[v,u]-=x
    S=L[:16,:16]-L[:16,16:]@np.linalg.solve(L[16:,16:],L[16:,:16]); return -S
def phi_g_H(C,th):
    tt=np.concatenate([[0.0],th]); phi=0; g=np.zeros(16); H=np.zeros((16,16))
    for i in range(16):
        for j in range(i+1,16):
            c=C[i,j]; d=tt[j]-tt[i]
            phi+=2*c*(1-np.cos(2*np.pi*d)); gd=4*np.pi*c*np.sin(2*np.pi*d); g[j]+=gd; g[i]-=gd
            h=8*np.pi**2*c*np.cos(2*np.pi*d); H[i,i]+=h;H[j,j]+=h;H[i,j]-=h;H[j,i]-=h
    return phi,g[1:],H[1:,1:]
for name,x in (('slsqp',th),('D2sym',th2)):
    w,s=fitw(x); C=schur(w); phi,g,H=phi_g_H(C,x)
    ev=np.linalg.eigvalsh(H)
    print(name,'sqrt s %.16f'%np.sqrt(s),'phi %.3e'%(phi-s),'|g| %.3e'%np.abs(g).max(),'eig',ev[:5],ev[-1], 'minw',np.sort(w)[:14])
np.save('d2_th.npy',th2)
