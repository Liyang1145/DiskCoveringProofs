"""Numerical radial-measure probe after a uniform interior-activity bound.

LP output is a proposal only, not an accepted impossibility certificate.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import math
import hashlib
import numpy as np
from scipy.optimize import linprog

ROOT=Path(__file__).resolve().parent
N21=ROOT.parent.parent/"n21-global"


def cap_matrix(rhos,ts,U):
    rho=np.asarray(rhos)[:,None];t=np.asarray(ts)[None,:]
    with np.errstate(divide="ignore",invalid="ignore"):
        c=(rho*rho+t*t-U*U)/(2*rho*t)
    result=np.arccos(np.clip(c,-1,1))/math.pi
    result=np.where(rho+t<=U,1.,result)
    result=np.where(np.abs(rho-t)>U,0.,result)
    result[0,:]=np.where(ts<=U,1.,0.) if rhos[0]==0 else result[0,:]
    return result


def main():
    U=F("0.262845072403585");Q=F(2771,5000)
    H=1-Q+2*Q*U
    assert H<1-U
    uf=float(U)
    ts=np.unique(np.r_[np.linspace(.05,1.,301),float(1-2*U),.6,.7,.8,.9,1.])
    ring=np.linspace(float(1-U),math.sqrt(1-uf*uf),1501)
    inner=np.linspace(0,float(H),2001)
    rb=cap_matrix(ring,ts,uf);ri=cap_matrix(inner,ts,uf)
    count=len(ts)
    rows=np.zeros((len(ring)+len(inner),count+2))
    rows[:len(ring),:count]=rb;rows[:len(ring),count]=-1
    rows[len(ring):,:count]=ri;rows[len(ring):,count+1]=-1
    objective=np.r_[np.zeros(count),14.,7.]
    equal=np.r_[np.ones(count),0.,0.][None,:]
    result=linprog(objective,A_ub=rows,b_ub=np.zeros(len(rows)),A_eq=equal,b_eq=[1.],
                   bounds=[(0,None)]*(count+2),method="highs")
    assert result.success
    chosen=[{"t":str(float(t)),"weight_float":float(w)} for t,w in zip(ts,result.x[:count]) if w>1e-9]
    fine_r=np.linspace(float(1-U),math.sqrt(1-uf*uf),10001)
    fine_i=np.linspace(0,float(H),10001)
    active=np.array([float(row["t"]) for row in chosen])
    weights=np.array([row["weight_float"] for row in chosen])
    demand=14*np.max(cap_matrix(fine_r,active,uf)@weights)+7*np.max(cap_matrix(fine_i,active,uf)@weights)
    output={"N":21,"B":14,"radius":str(U),"six_aux_bound":str(Q),"uniform_interior_radius_bound":str(H),
            "LP_objective_float":float(result.fun),"fine_grid_objective_float":float(demand),
            "atoms":chosen,"proved_exclusion":False,"numeric_only":True,
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    target=ROOT/"evidence/classified-capacity-numeric.json"
    assert not target.exists()
    target.write_text(json.dumps(output,indent=2),encoding="utf8")
    print(json.dumps(output,indent=2),flush=True)


if __name__=="__main__":
    main()
