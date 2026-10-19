"""Checker B: independent of certA/hp/geom/prop code paths (reads only raw JSON inputs).
mpmath interval arithmetic (iv, 420 bits), star-mesh (Kron) elimination, exact Fraction
elimination for PSD, exact breakpoint-maximised Lagrangian LP. Re-derives R = Q6 ∩ 1669 from
certs/1669.json's tree, re-derives shells/slabs and b-ranges, checks piece contiguity."""
import json, sys, os, glob, time
from fractions import Fraction as F
from mpmath import iv, mp
iv.prec=420
ROOT='/workspace/work/dcp-n26'
E=[tuple(e) for e in json.load(open(ROOT+'/model134.json'))['edges']]
K=json.load(open(ROOT+'/kkt2_122.json')); nX=2*len(K['live'])
CS=[F(x) for x in K['z'][:15]]
L0=[F(0)]*134
for e,x in zip(K['A'],K['z'][15+nX:15+nX+len(K['A'])]):
    if F(x)>F(1,10**40): L0[e]=F(x)
PJ=json.load(open(ROOT+'/local/prop.json')); TAU=[F(x) for x in PJ['tau0']]; V=[F(x) for x in PJ['v']]
RUP=F("0.234700090400448239616790133776692127560495963654971391785925")
def I(x): return iv.mpf([mp.mpf(x.numerator)/x.denominator]) if False else iv.mpf(x.numerator)/iv.mpf(x.denominator)
def MF(x):
    sg,man,ex,bc=mp.mpf(x)._mpf_
    v=F(int(man)*2**ex) if ex>=0 else F(int(man),2**(-ex))
    return -v if sg else v
def lo_(x): return MF(x.a)
def hi_(x): return MF(x.b)
mp.prec=420
def kron(w):
    """star-mesh elimination of every free vertex (intervals) -> anchor pair weights."""
    adj={}
    for (u,v),x in zip(E,w):
        if x==0: continue
        X=I(x); adj.setdefault(u,{}); adj.setdefault(v,{})
        adj[u][v]=adj[u].get(v,iv.mpf(0))+X; adj[v][u]=adj[v].get(u,iv.mpf(0))+X
    for k in sorted(k for k in adj if k>=16):
        nb=adj.pop(k); s=sum(nb.values(),iv.mpf(0)); ks=list(nb)
        for a in ks: adj[a].pop(k)
        for i,a in enumerate(ks):
            for b in ks[i+1:]:
                y=nb[a]*nb[b]/s
                adj[a][b]=adj[a].get(b,iv.mpf(0))+y; adj[b][a]=adj[b].get(a,iv.mpf(0))+y
    return {(i,j):adj[i][j] for i in range(16) for j in adj.get(i,{}) if j>i}
def elim_psd(M):
    n=len(M); M=[r[:] for r in M]
    for k in range(n):
        p=M[k][k]
        if p<0: return False
        rows=[i for i in range(k+1,n) if M[i][k]!=0]
        if p==0 and rows: return False
        for i in rows:
            f=M[i][k]/p
            for j in range(k+1,n): M[i][j]-=f*M[k][j]
    return True
def lp_exact(l,dlo,dhi,v,ba,bb):
    """max over nu of concave piecewise-linear dual; checks every breakpoint."""
    def val(nu):
        return sum(min((a-nu*b)*x,(a-nu*b)*y) for a,b,x,y in zip(l,v,dlo,dhi))+min(nu*ba,nu*bb)
    bps=[F(0)]+[a/b for a,b in zip(l,v) if b!=0]
    return max(val(nu) for nu in bps)
def check_leaf(w,lo,hi,ba,bb,mu):
    n=15; dlo=[a-c for a,c in zip(lo,CS)]; dhi=[b-c for b,c in zip(hi,CS)]
    r=[max(-a,b,abs(a),abs(b)) for a,b in zip(dlo,dhi)]; rt=[F(0)]+r
    pc=kron(w); W=sum(w,F(0)); t=[F(0)]+CS
    pi=iv.pi; phi=iv.mpf(0); g=[iv.mpf(0)]*16; H=[[iv.mpf(0)]*16 for _ in range(16)]; c3=iv.mpf(0)
    for (i,j),c in pc.items():
        a=2*pi*I(t[j]-t[i]); cs=iv.cos(a); sn=iv.sin(a)
        phi+=2*c*(1-cs); gd=4*pi*c*sn; g[j]+=gd; g[i]-=gd
        h=8*pi*pi*c*cs; H[i][i]+=h; H[j][j]+=h; H[i][j]-=h; H[j][i]-=h
        c3+=16*pi**3*c*I((rt[i]+rt[j])**3)/6
    g=g[1:]; H=[x[1:] for x in H[1:]]
    Vi=[I(x) for x in V]; mi=I(mu)
    Hx=[[H[i][j]+2*mi*Vi[i]*Vi[j] for j in range(n)] for i in range(n)]
    Hq=[[MF(Hx[min(i,j)][max(i,j)].mid) for j in range(n)] for i in range(n)]
    err=max(max(hi_(Hx[i][j])-Hq[i][j],Hq[i][j]-lo_(Hx[i][j])) for i in range(n) for j in range(n))
    if not elim_psd(Hq): return None
    gx=[g[i]-I(mu*(ba+bb))*Vi[i] for i in range(n)]
    gq=[MF(x.mid) for x in gx]; ge=[max(hi_(x)-q,q-lo_(x)) for x,q in zip(gx,gq)]
    # proposer: cyclic coordinate descent on convex quadratic + slab penalty (floats)
    s=float(max(r)); Hf=[[float(x)*s for x in row] for row in Hq]; gf=[float(x) for x in gq]
    lf=[float(x)/s for x in dlo]; hf=[float(x)/s for x in dhi]; vf=[float(x)*s for x in V]
    import numpy as np
    from scipy.optimize import minimize
    Hn=np.array(Hf); gn=np.array(gf)*1.0; vn=np.array(vf); sc=max(1e-300,float(np.abs(Hn).max()))
    fa,fb=float(ba),float(bb)
    obj=lambda y:(gn@y*s+0.5*y@Hn@y*s)/ (sc*s)
    jac=lambda y:(gn*s+Hn@y*s)/(sc*s)
    y0=np.clip(np.zeros(n),lf,hf)
    res=minimize(obj,y0,jac=jac,method='SLSQP',bounds=list(zip(lf,hf)),
        constraints=[{'type':'ineq','fun':lambda y:(vn@y-fa)/s,'jac':lambda y:vn/s},{'type':'ineq','fun':lambda y:(fb-vn@y)/s,'jac':lambda y:-vn/s}],
        options={'maxiter':500,'ftol':1e-15})
    y=list(res.x)
    ds=[min(max(F(round(yi*1e11))/10**11*F(s),a),b) for yi,a,b in zip(y,dlo,dhi)]
    Hd=[sum(Hq[i][j]*ds[j] for j in range(n)) for i in range(n)]
    q=sum(gq[i]*ds[i] for i in range(n))+sum(ds[i]*Hd[i] for i in range(n))/2
    l=[gq[i]+Hd[i] for i in range(n)]
    low=q+lp_exact(l,dlo,dhi,V,ba,bb)-sum(l[i]*ds[i] for i in range(n))+mu*ba*bb
    sr=sum(r); low-=err*sr*sr/2+sum(e*x for e,x in zip(ge,r))
    tot=phi-I(W)*I(RUP)*I(RUP)+I(low)-c3
    return lo_(tot)
# ---------- geometry, re-derived ----------
def region_R():
    c=json.load(open(ROOT+'/certs/1669.json')); lo=[F(x) for x in c['lower']]; hi=[F(x) for x in c['upper']]
    P=json.load(open(ROOT+'/pending.json'))['pending_closed_leaf_boxes']; b=[x for x in P if x['index']==1669][0]
    assert lo==[F(x) for x in b['lower']] and hi==[F(x) for x in b['upper']]
    opens=[]
    def walk(n,lo,hi):
        if n['kind']=='OPEN': opens.append((lo,hi)); return
        if n['kind']=='SPLIT':
            k=n['axis']; m=F(n['mid']); h1=list(hi); h1[k]=m; l2=list(lo); l2[k]=m
            walk(n['children'][0],lo,h1); walk(n['children'][1],l2,hi)
    walk(c['tree'],lo,hi); assert len(opens)==1 and c['open']==1
    return opens[0]
def shells(R):
    lo,hi=R; r0=F(66,10**7); out=[]; m=0
    def Q(m):
        r=r0/2**m; return [max(lo[k],CS[k]-r) if k>=6 else lo[k] for k in range(15)],[min(hi[k],CS[k]+r) if k>=6 else hi[k] for k in range(15)]
    assert Q(0)==(list(lo),list(hi))
    while True:
        a,b=Q(m); 
        if any(x>y for x,y in zip(a,b)): return out
        c,d=Q(m+1); a=list(a); b=list(b)
        if any(x>y for x,y in zip(c,d)): out.append((m,a,b)); m+=1; continue
        for k in range(6,15):
            if a[k]<c[k]: h=list(b); h[k]=c[k]; out.append((m,list(a),h)); a[k]=c[k]
            if b[k]>d[k]: l=list(a); l[k]=d[k]; out.append((m,l,list(b))); b[k]=d[k]
        m+=1
if __name__=='__main__':
    T0=time.time(); BUD=float(sys.argv[1])
    R=region_R(); SL=shells(R)
    st=ROOT+'/local/verB.json'; S=json.load(open(st)) if os.path.exists(st) else {'done':{},'min':None}
    files={}
    for f in glob.glob(ROOT+'/local/leaves/*.json'):
        d=json.load(open(f)); files[(d['m'],d['slab'])]=d
    cnt={}
    for (m,lo,hi) in SL:
        cnt[m]=cnt.get(m,-1)+1; key=f'{m}_{cnt[m]}'
        if key in S['done']: continue
        if time.time()-T0>BUD: break
        d=files[(m,cnt[m])]
        assert [F(x) for x in d['lower']]==lo and [F(x) for x in d['upper']]==hi, key
        b1=sum(min(v*(a-c),v*(b-c)) for v,a,b,c in zip(V,lo,hi,CS)); b2=sum(max(v*(a-c),v*(b-c)) for v,a,b,c in zip(V,lo,hi,CS))
        ps=d['pieces']; assert F(ps[0]['ba'])<=b1 and F(ps[-1]['bb'])>=b2
        for p,q in zip(ps,ps[1:]): assert p['bb']==q['ba']
        mu=F(d['mu']); assert mu>=0; worst=None
        for p in ps:
            assert 'OPEN' not in p
            kap=F(p['kappa']); w=[a+kap*t for a,t in zip(L0,TAU)]; assert all(x>=0 for x in w)
            bd=check_leaf(w,lo,hi,F(p['ba']),F(p['bb']),mu)
            assert bd is not None and bd>0, (key,p['ba'])
            worst=bd if worst is None else min(worst,bd)
        S['done'][key]={'pieces':len(ps),'min':str(worst)}
        json.dump(S,open(st+'.tmp','w')); os.replace(st+'.tmp',st)
    print('slabs total',len(SL),'verified',len(S['done']),'min', min(float(F(v['min'])) for v in S['done'].values()) if S['done'] else None)
