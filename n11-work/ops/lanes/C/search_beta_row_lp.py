#!/usr/bin/env python3
"""Search beta and arbitrary nonnegative DBM rows in every sign region.

The float LP is only a candidate generator. A reported PASS must survive the
exact Fraction recheck of f0, all nine g values, reduced rows, and T^2.
"""
from fractions import Fraction as Q
import argparse, hashlib, json, math, sys, time
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common
IDS = (1409, 2337, 2341, 2356, 2360, 2368, 2370)
OUT = HERE / "beta-row-lp-results.json"

def coeffs(rec, weights):
    pairs = [(k // 9, k % 9) for k in range(81)]
    # Reuse the certificate's 36 unordered line pairs.
    P = [(i,j) for i in range(9) for j in range(i+1,9)]
    s = [Q(str(p["s"])) for p in rec["packets"]]
    c = [Q(str(p["c"])) for p in rec["packets"]]
    cl = [sum(Q(str(weights[f][k]))/10**12*s[k]*(P[k][0]-P[k][1])
              for k in range(36)) for f in range(16)]
    f0c = [sum(Q(str(weights[f][k]))/10**12*c[k] for k in range(36))
           for f in range(16)]
    g = [[sum(Q(str(weights[f][k]))/10**12*s[k] for k in range(36)
              if P[k][0] <= q < P[k][1]) for f in range(16)] for q in range(9)]
    return cl, f0c, g

def exact_eval(rec, weights, beta, lam, rmin, db):
    clc, f0c, gc = coeffs(rec, weights)
    cl = sum(beta[f]*clc[f] for f in range(16))
    f0 = sum(beta[f]*f0c[f] for f in range(16)) + (common.LQ if cl < 0 else Q(2*Q(1150475603510479590494077,2951479051793528258560000)))*cl
    g = [sum(beta[f]*gc[q][f] for f in range(16)) for q in range(9)]
    ep = [common.endpoint_lo(x) for x in g]
    reduced = []
    for q in range(9):
        rho = sum(lam[k]*common.row_a(*common.PAIRS[k],q) for k in range(90))
        reduced.append(rmin <= ep[q] + rho)
    lower = f0 - sum(lam[k]*Q(db[i][j],4096) for k,(i,j) in enumerate(common.PAIRS)) + rmin
    return {"cl":str(cl),"g":[str(x) for x in g],"f0Lo":str(f0),
            "rmin":str(rmin),"lower":str(lower),"gap":str(lower-common.T2),
            "reduced":all(reduced),"pass":lower>common.T2 and all(reduced)}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--time-budget",type=float,default=90); ap.add_argument("--ids",default=",".join(map(str,IDS)))
    a=ap.parse_args(); start=time.monotonic()
    import numpy as np
    from scipy.optimize import linprog
    doc=json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig")); weights=doc["weights"]
    text=common.DBM.read_text(); out=[]
    for rid in [int(x) for x in a.ids.split(',')]:
        rec=next(r for r in doc["records"] if r["id"]==rid); db=common.parse_db(text,rid)
        clc,f0c,gc=coeffs(rec,weights)
        best=None; branches=0
        for mask in range(512):
            if time.monotonic()-start>a.time_budget:
                print('TIME_LIMIT',rid,branches); break
            signs=[1 if mask>>q&1 else -1 for q in range(9)]; cpos=bool(mask>>9&1)
            # objective: f0 - lamB + rmin
            obj=np.zeros(107)
            for f in range(16): obj[f]=-(f0c[f]+(common.LQ if not cpos else Q(2*Q(1150475603510479590494077,2951479051793528258560000)))*clc[f])
            for k,(i,j) in enumerate(common.PAIRS): obj[16+k]=db[i][j]/4096
            obj[-1]=-1
            A=[]; b=[]
            for q in range(9):
                row=np.zeros(107); row[-1]=1
                for k in range(90): row[16+k]=-common.row_a(*common.PAIRS[k],q)
                for f in range(16): row[f]=-gc[q][f]
                A.append(row); b.append(0)
            row=np.zeros(107)
            for f in range(16): row[f]=-clc[f] if cpos else clc[f]
            A.append(row); b.append(0)
            for q in range(9):
                row=np.zeros(107)
                for f in range(16): row[f]=-signs[q]*gc[q][f]
                A.append(row); b.append(0)
            eq=np.zeros((1,107)); eq[0,:16]=1
            lp=linprog(obj,A_ub=np.array(A),b_ub=np.array(b),A_eq=eq,b_eq=[1],bounds=[(0,None)]*16+[(0,None)]*90+[(None,None)],method='highs')
            branches+=1
            if lp.success and (best is None or lp.fun<best.fun): best=lp
        row={"id":rid,"branches":branches,"float_success":best is not None,"status":"no candidate"}
        if best is not None:
            beta=[Q(float(v)).limit_denominator(10**12) for v in best.x[:16]]
            beta=[max(Q(0),v) for v in beta]; sb=sum(beta); beta=[v/sb for v in beta]
            lam=[Q(float(v)).limit_denominator(10**18) if v>1e-12 else Q(0) for v in best.x[16:106]]
            # LP rmin can round below an active reduced-row RHS.  Recompute
            # the exact maximum feasible rmin for the rounded beta and lam.
            gexact=[sum(beta[f]*gc[q][f] for f in range(16)) for q in range(9)]
            rmin=min(common.endpoint_lo(gexact[q]) +
                     sum(lam[k]*common.row_a(*common.PAIRS[k],q) for k in range(90))
                     for q in range(9))
            ex=exact_eval(rec,weights,beta,lam,rmin,db)
            row.update(float_lower=str(-best.fun),float_gap=str(-Q(str(best.fun))-common.T2),float_pass=(-best.fun)>float(common.T2),beta=[str(v) for v in beta],lam_nonzero=[[list(common.PAIRS[k]),str(lam[k])] for k in range(90) if lam[k]],exact=ex,status="PASS" if ex["pass"] else "candidate")
        out.append(row); print(rid,row["status"],row.get("float_success"),row.get("exact",{}).get("gap"))
    result={"scope":"float sign-region LP candidate plus exact Fraction recheck; no kernel credit","proposal_sha256":hashlib.sha256(common.PROPOSAL.read_bytes()).hexdigest().upper(),"records":out,"pass_count":sum(r["status"]=="PASS" for r in out)}
    OUT.write_text(json.dumps(result,indent=1)+"\n"); print('pass_count',result["pass_count"])
if __name__=='__main__': main()
