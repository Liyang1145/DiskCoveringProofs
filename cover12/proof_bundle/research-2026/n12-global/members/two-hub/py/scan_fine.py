import sys, math, json, time
from pathlib import Path
import numpy as np
HERE = Path("research-2026/n12-global/members/two-hub/py").resolve()
sys.path.insert(0, str(HERE))
import dual2 as D2
U = D2.U
def beta(t,a):
    if t<=0: return math.pi
    if t+a<=U: return math.pi
    if abs(t-a)>=U: return 0.0
    return math.acos(max(-1,min(1,(t*t+a*a-U*U)/(2*t*a))))
a=1-2*U; tmax=1-U-1e-7
ts=[]; x=0.0
while x<tmax: ts.append(round(x,6)); x+=0.025
ts.append(tmax)
cfgs=[]
for t1 in ts:
    for t2 in ts:
        if t2<t1-1e-15: continue
        b1,b2=beta(t1,a),beta(t2,a); dmin=max(0.0,2*math.pi-b1-b2)
        cands={round(dmin,6), round(math.pi,6)}
        if dmin<math.pi: cands.add(round((dmin+math.pi)/2,6)); cands.add(round(dmin+0.25,6))
        for dl in sorted(cands):
            if dl>math.pi+1e-12: continue
            if (t1+a<=U) or (t2+a<=U) or (b1+b2>=2*math.pi-dl-1e-12): cfgs.append((t1,t2,dl))
print("fine grid configs:",len(cfgs))
rows=[]; t0=time.time()
for (t1,t2,dl) in cfgs:
    r=D2.solve(t1,t2,dl,K=4,sincos=True,n_rho=40,n_phi=144,clip_req=False)
    rows.append(dict(t1=t1,t2=t2,delta=dl,ok=r.get("ok",False),m_star=r.get("m_star")))
ms=[r["m_star"] for r in rows if r["ok"]]
print("done %.1fs  tested %d  fails %d  m* in [%.5f, %.5f]"%(time.time()-t0,len(rows),len([r for r in rows if not r["ok"]]),min(ms),max(ms)))
worst=sorted([r for r in rows if r["ok"]],key=lambda r:-r["m_star"])[:6]
for r in worst: print("  worst t1=%.4f t2=%.4f dl=%.4f m*=%.5f"%(r["t1"],r["t2"],r["delta"],r["m_star"]))
ref=[]
for r in worst:
    sol=D2.solve(r["t1"],r["t2"],r["delta"],K=4,sincos=True,n_rho=40,n_phi=144,clip_req=False)
    val,arg=D2.refine_max(sol,sol["m_basis"],K=4,sincos=True,n_start=20)
    req=float(sol["req"]@sol["m_basis"])
    ref.append(dict(t1=r["t1"],t2=r["t2"],delta=r["delta"],m_grid=r["m_star"],m_local=val,arg=list(arg),ratio=10*val/req))
    print("  refined t1=%.4f t2=%.4f dl=%.4f  m_grid=%.6f m_local=%.6f ratio=%.6f"%(r["t1"],r["t2"],r["delta"],r["m_star"],val,10*val/req))
json.dump(dict(rows=rows,refined=ref),open("research-2026/n12-global/members/two-hub/evidence/dual_fine_scan.json","w"),indent=1)
