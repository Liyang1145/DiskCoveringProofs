import sys, math, json, time
from pathlib import Path
HERE = Path("research-2026/n12-global/members/two-hub/py").resolve()
sys.path.insert(0, str(HERE))
import dual_refine as D
U = D.U
def beta(t,a):
    if t<=0: return math.pi
    if t+a<=U: return math.pi
    if abs(t-a)>=U: return 0.0
    return math.acos(max(-1,min(1,(t*t+a*a-U*U)/(2*t*a))))
a=1-2*U
ts=[]; x=0.0
while x < 2.0/3.0 - 1e-6:
    ts.append(round(x,6)); x += 0.04
ts.append(2.0/3.0-1e-6)
rows=[]; t0=time.time()
for t1 in ts:
    for t2 in ts:
        if t2<t1: continue
        b1,b2=beta(t1,a),beta(t2,a)
        dmin=max(0.0,2*math.pi-b1-b2)
        cand=set([round(dmin,6)])
        if dmin<math.pi: cand.add(round((dmin+math.pi)/2,6))
        cand.add(round(math.pi,6))
        for dl in sorted(cand):
            if dl>math.pi+1e-12: continue
            ok = (t1+a<=U) or (t2+a<=U) or (b1+b2 >= 2*math.pi-dl-1e-12)
            if not ok: continue
            m,st = D.solve(t1,t2,dl,K=4,n_rho=40,n_phi=144,sincos=True)
            rows.append(dict(t1=t1,t2=t2,delta=dl,m_star=m,status=st,beta1=b1,beta2=b2))
bad=[r for r in rows if r["m_star"] is None or r["m_star"]>=0.1]
ms=[r["m_star"] for r in rows if r["m_star"] is not None]
print("domain t<2/3: tested %d  fail %d  min %.5f max %.5f  (%.1fs)"%(len(rows),len(bad),min(ms),max(ms),time.time()-t0))
for r in sorted(rows,key=lambda r:-(r["m_star"] or 0))[:12]:
    print("  worst t1=%.4f t2=%.4f delta=%.4f m*=%.5f"%(r["t1"],r["t2"],r["delta"],r["m_star"]))
for r in bad[:10]:
    print("  FAIL t1=%.4f t2=%.4f delta=%.4f m*=%s"%(r["t1"],r["t2"],r["delta"],r["m_star"]))
json.dump(rows,open("research-2026/n12-global/members/two-hub/evidence/dual_scan_sin.json","w"),indent=1)
