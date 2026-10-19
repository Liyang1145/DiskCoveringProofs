"""FLOAT ESTIMATE (not a certificate) of the archive refined-pinning bound
(verify_refined_anchor_pinning.derive) for a given anchor-angle box, using the
published proposal network (92 rods, reference p, weights).  Geometry rounding
term and exact arc extrema are approximated (reference points used as root)."""
import json, math, numpy as np, sys
from fractions import Fraction as F
P=json.load(open('repo/cover26/proof_bundle/work/n26-refined-anchor-pinning-broad-proposal-v2.json'))
sc=int(P['rational_scale']); p=np.array([[int(a)/sc,int(b)/sc] for a,b in P['reference_numerators']])
w=np.array([int(x)/sc for x in P['weight_numerators']]); E=[tuple(e) for e in P['edges']]
RS2=0.234700090400448239616790133776692127560495963654971391785925**2
cells=[(float(F(a)),float(F(b))) for a,b in P['closed_anchor_angle_cells']]
ang=[0.0]+[math.atan2(p[a,1],p[a,0])/(2*math.pi)%1 for a in range(1,16)]
def arc_eps(lo,hi,a):
    ts=np.linspace(lo,hi,2001); pts=np.stack([np.cos(2*np.pi*ts),np.sin(2*np.pi*ts)],1)
    return np.sqrt(((pts-p[a])**2).sum(1)).max()
def bound(cellbox):
    eps=[0.0]+[arc_eps(lo,hi,a+1) for a,(lo,hi) in enumerate(cellbox)]
    res=np.zeros_like(p); E0=0
    for (u,v),x in zip(E,w):
        d=p[u]-p[v]; E0+=x*d@d; res[u]+=x*d; res[v]-=x*d
    rn=np.abs(res).sum(1)
    # shortest-path resistances
    n=len(p); adj=[[] for _ in range(n)]
    for (u,v),x in zip(E,w): adj[u].append((v,1/x)); adj[v].append((u,1/x))
    val=[0.0 if i<16 else None for i in range(n)]; par=[None]*n; todo=set(range(n))
    while todo:
        u=min([i for i in todo if val[i] is not None],key=lambda i:(val[i],i)); todo.remove(u)
        for v,c in adj[u]:
            if v in todo and (val[v] is None or val[u]+c<val[v]): val[v]=val[u]+c; par[v]=u
    anc=list(range(16))
    for v in range(16,n):
        c=v
        while c>=16: c=par[c]
        anc.append(c)
    corr=0; rad=[]; nonr=[]
    for v in range(16):
        L2=p[v]@p[v]; k=res[v]@p[v]/L2; rad.append(k); nonr.append(np.abs(res[v]-k*p[v]).sum()); corr+=k*(L2-1)
    K=2*sum(rn[v]*math.sqrt(val[v]) for v in range(16,n))
    A=RS2*w.sum()-E0+corr+sum(k*e*e+2*r*e for k,r,e in zip(rad,nonr,eps))+2*sum(rn[v]*eps[anc[v]] for v in range(16,n))
    Y=K+math.sqrt(max(A,0))
    errs=[eps[anc[16+i]]+math.sqrt(val[16+i])*Y for i in range(26)]
    return max(errs), A, K
allow=7/800000
print('published cell: est max center error %.4e (archive states < 3.684e-6)'%bound(cells)[0])
mid=[(a+b)/2 for a,b in cells]
for hw in [9e-8,2e-7,5e-7,1e-6,3e-6,6.4e-6]:
    box=[(m-hw,m+hw) if k>=6 else cells[k] for k,m in enumerate(mid)]
    e,A,K=bound(box); print('half-width %.1e on 9 wide axes: est max center error %.3e  (allowance %.3e) %s'%(hw,e,allow,'OK' if e<allow else 'EXCEEDS'))
import shells1669 as S
print('--- using exact 1669 ∩ Q_j boxes ---')
for j in [1,2,3,4,5,6]:
    lo,hi=S.Q(j); box=[(float(l),float(h)) for l,h in zip(lo,hi)]
    e,A,K=bound(box); print('Q_%d (half-width %.1e): est max center error %.3e %s'%(j,2**j*1e-7,e,'OK' if e<allow else 'EXCEEDS'))
