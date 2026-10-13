import sys, math, json
from pathlib import Path
import numpy as np
HERE = Path("research-2026/n12-global/members/two-hub/py").resolve()
sys.path.insert(0, str(HERE))
import dual2 as D2
U = D2.U
cfgs = [(0.175,0.200,3.0377), (0.200,0.200,3.0223), (0.175,0.225,3.1362), (0.150,0.200,2.8931)]
rows=[]
for (t1,t2,dl) in cfgs:
    for K in (4,6,8):
        sol = D2.solve(t1,t2,dl,K=K,sincos=True,n_rho=40,n_phi=144,clip_req=False)
        if not sol.get("ok"): 
            print("cfg",t1,t2,dl,"K",K,"FAIL",sol.get("msg")); continue
        val,arg = D2.refine_max(sol, sol["m_basis"], K=K, sincos=True, n_start=24)
        req = float(sol["req"] @ sol["m_basis"])
        rows.append(dict(t1=t1,t2=t2,delta=dl,K=K,m_grid=sol["m_star"],m_local=val,ratio=10*val/req,arg=list(arg)))
        print("t1=%.3f t2=%.3f dlt=%.4f K=%d  m_grid=%.6f m_local=%.6f ratio=%.6f"%(t1,t2,dl,K,sol["m_star"],val,10*val/req), flush=True)
json.dump(rows,open("research-2026/n12-global/members/two-hub/evidence/dual_degree_test.json","w"),indent=1)
