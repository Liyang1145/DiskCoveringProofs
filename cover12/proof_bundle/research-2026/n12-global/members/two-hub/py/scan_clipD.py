import sys, math, json, time
from pathlib import Path
import numpy as np
HERE = Path("research-2026/n12-global/members/two-hub/py").resolve()
sys.path.insert(0, str(HERE))
import dual_refine as D
from scipy.optimize import linprog
U = D.U

def basis_arc(center, half, K, sincos=True):
    n = 1 + K*(2 if sincos else 1); b = np.zeros(n); b[0]=2.0*half
    for k in range(1,K+1):
        b[k] = (math.sin(k*(center+half))-math.sin(k*(center-half)))/k
        if sincos: b[K+k] = -(math.cos(k*(center+half))-math.cos(k*(center-half)))/k
    return b

def arc_cap_basis(cA,hA,cB,hB,K):
    n = 1 + K*2
    d = D.wrap(cA-cB); lo = max(-hB, d-hA); hi = min(hB, d+hA)
    if hi<=lo: return np.zeros(n)
    return basis_arc(cB+0.5*(lo+hi), 0.5*(hi-lo), K, True)

def build2(t1,t2,delta,K=4,n_rho=40,n_phi=144,clipD=True):
    h1 = np.array([t1,0.0]); h2 = t2*np.array([math.cos(delta), math.sin(delta)])
    d = float(np.hypot(*(h1-h2)))
    b = math.acos(max(-1.0,min(1.0,d/(2*U)))) if d>0 else math.pi/2
    away1 = math.atan2(*(h1-h2)[::-1]) if d>0 else 0.0
    away2 = math.atan2(*(h2-h1)[::-1]) if d>0 else math.pi
    per = 1+2*K; nw = 3*per
    req = np.zeros(nw); req[0:per] = basis_arc(0.0, math.pi, K, True)
    for j,(hj,aw) in enumerate(((h1,away1),(h2,away2))):
        tj = float(np.hypot(*hj)); base = math.atan2(hj[1],hj[0]) if tj>0 else 0.0
        lo,hi = aw-(math.pi-b), aw+(math.pi-b)
        if clipD and tj + U > 1.0:
            z = (1.0 - tj*tj - U*U)/(2*tj*U)
            th0 = math.acos(max(-1.0,min(1.0,z)))
            lo2,hi2 = (base+math.pi)-(math.pi-th0), (base+math.pi)+(math.pi-th0)
            dd = D.wrap(lo-lo2); a=lo2+max(-(math.pi-th0), dd-(hi-lo)/2.0); a2=lo2+min((math.pi-th0), dd+(hi-lo)/2.0)
            lo,hi = a,a2
        req[(j+1)*per:(j+2)*per] += basis_arc(0.5*(lo+hi), 0.5*(hi-lo), K, True) if hi>lo else 0.0
    rows=[]
    for rho in np.linspace(1.0-U, math.sqrt(1.0-U*U), n_rho):
        ah = math.acos(max(-1,min(1,(1+rho*rho-U*U)/(2*rho)))) 
        for phi in np.linspace(0,2*math.pi,n_phi,endpoint=False):
            c = rho*np.array([math.cos(phi), math.sin(phi)]); row = np.zeros(nw)
            row[0:per] += basis_arc(phi, ah, K, True)
            for j,hj in enumerate((h1,h2)):
                ell = float(np.hypot(*(c-hj)))
                if ell < 2*U:
                    bet = math.acos(max(-1,min(1,ell/(2*U)))); psi = math.atan2(*(c-hj)[::-1])
                    row[(j+1)*per:(j+2)*per] += arc_cap_basis(psi,bet,away1 if j==0 else away2, math.pi-b, K)
            rows.append(row)
    return np.array(rows), req

def solve2(t1,t2,delta,K=4,n_rho=40,n_phi=144,clipD=True):
    A, req = build2(t1,t2,delta,K,n_rho,n_phi,clipD)
    nr,nw = A.shape; per = nw//3; ncoef = per-1
    nvar = nw + 3*ncoef + 1; mi = nw+3*ncoef
    A_ub = np.zeros((nr,nvar)); A_ub[:,0:nw] = A; A_ub[:,mi] = -1.0; b_ub = np.zeros(nr)
    rows2,b2 = [],[]
    for j in range(3):
        r=np.zeros(nvar); r[j*per]=-1.0
        for k in range(ncoef): r[nw+j*ncoef+k]=1.0
        rows2.append(r); b2.append(0.0)
        for k in range(ncoef):
            r1=np.zeros(nvar); r1[j*per+1+k]=1.0; r1[nw+j*ncoef+k]=-1.0; rows2.append(r1); b2.append(0.0)
            r2=np.zeros(nvar); r2[j*per+1+k]=-1.0; r2[nw+j*ncoef+k]=-1.0; rows2.append(r2); b2.append(0.0)
    A_ub=np.vstack([A_ub,np.array(rows2)]); b_ub=np.concatenate([b_ub,np.array(b2)])
    A_eq=np.zeros((1,nvar)); A_eq[0,0:nw]=req; b_eq=np.array([1.0])
    c=np.zeros(nvar); c[mi]=1.0
    bounds=[(0.0,None)]+[(None,None)]*(per-1)+[(None,None)]*(2*per)+[(0.0,None)]*(3*ncoef)+[(0.0,None)]
    res=linprog(c,A_ub=A_ub,b_ub=b_ub,A_eq=A_eq,b_eq=b_eq,bounds=bounds,method="highs")
    return (float(res.fun) if res.status==0 else None)

def beta(t,a):
    if t<=0: return math.pi
    if t+a<=U: return math.pi
    if abs(t-a)>=U: return 0.0
    return math.acos(max(-1,min(1,(t*t+a*a-U*U)/(2*t*a))))

a=1-2*U; ts=[]; x=0.0
while x < 2.0/3.0-1e-6: ts.append(round(x,6)); x+=0.04
ts.append(2.0/3.0-1e-6)
rows=[]; t0=time.time()
for t1 in ts:
    for t2 in ts:
        if t2<t1: continue
        b1,b2=beta(t1,a),beta(t2,a); dmin=max(0.0,2*math.pi-b1-b2)
        cand=set([round(dmin,6)]); cand.add(round(math.pi,6))
        if dmin<math.pi: cand.add(round((dmin+math.pi)/2,6))
        for dl in sorted(cand):
            if dl>math.pi+1e-12: continue
            if not ((t1+a<=U) or (t2+a<=U) or (b1+b2>=2*math.pi-dl-1e-12)): continue
            m = solve2(t1,t2,dl,clipD=True)
            m0 = solve2(t1,t2,dl,clipD=False)
            rows.append(dict(t1=t1,t2=t2,delta=dl,m_clip=m,m_noclip=m0,beta1=b1,beta2=b2))
bad=[r for r in rows if r["m_clip"] is None or r["m_clip"]>=0.1]
ms=[r["m_clip"] for r in rows if r["m_clip"] is not None]
print("clipD domain t<2/3: tested %d fail %d min %.5f max %.5f (%.1fs)"%(len(rows),len(bad),min(ms),max(ms),time.time()-t0))
for r in sorted(rows,key=lambda r:-(r["m_clip"] or 0))[:12]:
    print("  worst t1=%.4f t2=%.4f dlt=%.4f m_clip=%.5f m_noclip=%.5f"%(r["t1"],r["t2"],r["delta"],r["m_clip"],r["m_noclip"]))
for r in bad[:10]: print("  FAIL t1=%.4f t2=%.4f dlt=%.4f m*=%s"%(r["t1"],r["t2"],r["delta"],r["m_clip"]))
json.dump(rows,open("research-2026/n12-global/members/two-hub/evidence/dual_scan_clipD.json","w"),indent=1)
