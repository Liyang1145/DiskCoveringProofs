"""PROPOSAL ONLY: Newton on the full KKT system of min_theta,X max_e |p_u-p_v|^2
(all 134 rods active) near box 1669.  Unknowns z=(theta15, X120, lam134, s)."""
import json, numpy as np, mpmath as mp
M=json.load(open('model134.json')); E=[tuple(e) for e in M['edges']]
def F(z, lib=np):
    if lib is np:
        cos,sin,pi=np.cos,np.sin,np.pi
    else:
        cos,sin,pi=mp.cos,mp.sin,mp.pi
    th=[0]+list(z[:15]); X=z[15:135]; lam=z[135:269]; s=z[269]
    P=[(cos(2*pi*t),sin(2*pi*t)) for t in th]+[(X[2*i],X[2*i+1]) for i in range(60)]
    dP=[(-2*pi*sin(2*pi*t),2*pi*cos(2*pi*t)) for t in th]
    r1=[];gX=[[0,0] for _ in range(60)];gT=[0]*16
    for (u,v),l in zip(E,lam):
        dx=P[u][0]-P[v][0]; dy=P[u][1]-P[v][1]
        r1.append(dx*dx+dy*dy-s)
        for w,sg in ((u,1),(v,-1)):
            if w>=16: gX[w-16][0]+=2*l*sg*dx; gX[w-16][1]+=2*l*sg*dy
            else: gT[w]+=2*l*sg*(dx*dP[w][0]+dy*dP[w][1])
    return r1+[g for xy in gX for g in xy]+gT[1:]+[sum(lam)-1]
def J(z,h=1e-7):
    f0=np.array(F(z)); Jm=np.empty((270,270))
    for k in range(270):
        zp=z.copy(); zp[k]+=h; zm=z.copy(); zm[k]-=h
        Jm[:,k]=(np.array(F(zp))-np.array(F(zm)))/(2*h)
    return Jm
if __name__=='__main__':
    import certify_box as cb, kkt1669
    v=np.load('kkt1669_float.npy'); th=v[:15]; lam=v[15:]
    P,l2=kkt1669.harm(lam,th)
    z=np.concatenate([th,P[16:].ravel(),lam,[l2.mean()]])
    for it in range(12):
        f=np.array(F(z)); Jm=J(z); 
        dz=np.linalg.lstsq(Jm,-f,rcond=None)[0]; z=z+dz
        print(it,'|F|',np.abs(f).max(),'cond %.2e'%np.linalg.cond(Jm),'minlam',z[135:269].min(),flush=True)
    np.save('kkt_z.npy',z)
    t=np.concatenate([[0],z[:15]]); print('D2 dev',max(abs(t[k+8]-t[k]-0.5) for k in range(8)),'sqrt s',np.sqrt(z[269]))
