"""Checker A (flint/arb + exact Fractions) for LOCAL-SLAB leaves near theta*.
Leaf = (rational weights w>=0, closed box [lo,hi], rational vector v, interval [ba,bb] of
b = v.(theta - c*), mu>=0). Claim: Phi_w(theta) > W R*_up^2 for every theta in box with b in [ba,bb].
Proof chain: 3rd-order Taylor remainder at c* (rigorous arb), S-lemma term -mu(b-ba)(bb-b) <= 0,
exact-LDL PSD check of the rational midpoint of H+2mu vv^T (entry error charged), supporting
hyperplane at a float-proposed point, Lagrangian LP bound over box ∩ slab. Floats only propose."""
from fractions import Fraction as F
import numpy as np, hp
from flint import arb, fmpq
A=hp.A; PI=hp.PI
def fr(x):
    m,e=x.man_exp(); m=int(m); e=int(e); return F(m*2**e) if e>=0 else F(m,2**(-e))
def up(x): return fr(x.upper())
def lowf(x): return fr(x.lower())
def dy(x,bits=260):   # dyadic rounding of an arb midpoint
    return F(round(fr(x.mid())*2**bits),2**bits)
def psd(Hm):
    n=len(Hm); M=[r[:] for r in Hm]
    for k in range(n):
        p=M[k][k]
        if p<0: return False
        if p==0:
            if any(M[i][k]!=0 for i in range(k+1,n)): return False
            continue
        for i in range(k+1,n):
            if M[i][k]:
                f=M[i][k]/p
                for j in range(k,n): M[i][j]-=f*M[k][j]
    return True
def linmin(l,dlo,dhi,v,ba,bb):
    """exact lower bound of min l.d over {dlo<=d<=dhi, ba<=v.d<=bb} via best of several nu."""
    cands={F(0)}
    for li,vi in zip(l,v):
        if vi: cands.add(li/vi)
    def val(nu):
        s=sum(min((li-nu*vi)*a,(li-nu*vi)*b) for li,vi,a,b in zip(l,v,dlo,dhi))
        return s+min(nu*ba,nu*bb)
    # float screen then exact on best few
    cl=sorted(cands,key=lambda nu:-float(val(nu)))[:3] if len(cands)<40 else list(cands)
    return max(val(nu) for nu in cl)
def leaf_bound(w,lo,hi,v,ba,bb,mu,cache=None):
    c=hp.THSTAR; dlo=[a-x for a,x in zip(lo,c)]; dhi=[b-x for b,x in zip(hi,c)]
    r=[max(abs(a),abs(b)) for a,b in zip(dlo,dhi)]; rt=[F(0)]+r
    pairs,W=hp.pairs_arb(w)
    phi,g,H=hp.phi_g_H(pairs,c)
    C3=arb(0)
    for (i,j),cij in pairs.items(): C3+=cij*A((rt[i]+rt[j])**3)
    C3=C3*8*PI**3/3
    n=15; Va=[A(x) for x in v]; m2=2*A(mu)
    Hmod=[[H[i][j]+m2*Va[i]*Va[j] for j in range(n)] for i in range(n)]
    Hm=[[dy(Hmod[i][j]) for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i): Hm[i][j]=Hm[j][i]
    eps=max(up(abs(Hmod[i][j]-A(Hm[i][j]))) for i in range(n) for j in range(n))
    if not psd(Hm): return None,'not-psd'
    gm=[g[i]-A(mu*(ba+bb))*Va[i] for i in range(n)]
    gq=[dy(x) for x in gm]; gerr=[up(abs(x-A(q))) for x,q in zip(gm,gq)]
    # float proposal of convex minimiser (scaled)
    s=float(max(r)); Hf=np.array([[float(x) for x in row] for row in Hm])*s; gf=np.array([float(x) for x in gq])
    lf=np.array([float(x) for x in dlo])/s; hf=np.array([float(x) for x in dhi])/s; vf=np.array([float(x) for x in v])
    y=np.clip(np.zeros(n),lf,hf)
    L=np.linalg.eigvalsh(Hf).max()+1e-30; step=1/L
    for it in range(3000):   # projected gradient with slab penalty (proposal only)
        gr=gf+Hf@y; y=np.clip(y-step*gr,lf,hf)
        bv=vf@y*s
        if bv<float(ba): y=np.clip(y+(float(ba)-bv)/s*vf/(vf@vf),lf,hf)
        elif bv>float(bb): y=np.clip(y-(bv-float(bb))/s*vf/(vf@vf),lf,hf)
    ds=[max(a,min(b,F(int(round(yi*1e12)),10**12)*F(s))) for yi,a,b in zip(y,dlo,dhi)]
    Hd=[sum(Hm[i][j]*ds[j] for j in range(n)) for i in range(n)]
    qds=sum(gq[i]*ds[i] for i in range(n))+sum(ds[i]*Hd[i] for i in range(n))/2
    l=[gq[i]+Hd[i] for i in range(n)]
    lin=linmin(l,dlo,dhi,v,ba,bb)-sum(l[i]*ds[i] for i in range(n))
    sr=sum(r)
    tot=phi-A(W)*A(hp.RUP2)+A(mu*ba*bb+qds+lin-eps*sr*sr/2-sum(e*ri for e,ri in zip(gerr,r)))-C3
    return lowf(tot),W
