"""Standard-library exact contraction certificate for the 26-variable root."""
from pathlib import Path
from fractions import Fraction as Q
import json,sys,hashlib
from exact_model import build,N,NAMES
from rational_interval import I,S,evaluator

HERE=Path(__file__).resolve().parent

def demand(p,message):
    if not p:raise ValueError(message)

def certify(negative=False):
    proposal=json.loads((HERE/'root-proposal.json').read_text())
    demand(proposal['dimension']==N and proposal['coordinate_names']==NAMES,'model dimension')
    center=list(map(Q,proposal['center']));epsilon=Q(proposal['box_half_width'])
    if negative:center[13]+=Q(1,10**12)
    demand(len(center)==N and epsilon>0,'box dimension')
    Y=[[I(Q(x)) for x in row] for row in proposal['inverse_jacobian']]
    demand(len(Y)==N and all(len(row)==N for row in Y),'inverse dimension')
    box=[I(x-epsilon,x+epsilon) for x in center]
    _,_,F=build()
    eval_center=evaluator([I(x) for x in center]);eval_box=evaluator(box)
    residual=[eval_center(f) for f in F]
    J=[[eval_box(f.diff(i)) for i in range(N)] for f in F]
    eta=max(sum((Y[i][j]*residual[j] for j in range(N)),I(0)).abs_upper() for i in range(N))
    rows=[]
    for i in range(N):
        rows.append(sum((I(1 if i==k else 0)-sum((Y[i][j]*J[j][k] for j in range(N)),I(0))).abs_upper()
                        for k in range(N)))
    contraction=max(rows)
    demand(contraction<S,'contraction norm < 1')
    demand(Q(eta,S)+Q(contraction,S)*epsilon<epsilon,'self-map inside root box')
    # These coarse bounds keep the certificate easy to audit and avoid decimals in acceptance.
    demand(Q(eta,S)<Q(1,10**95),'center residual bound')
    demand(Q(contraction,S)<Q(1,10**60),'Jacobian contraction bound')
    legacy_lo=Q('0.234700090400448239616790133776692127560495963654971391785924')
    legacy_hi=Q('0.234700090400448239616790133776692127560495963654971391785925')
    demand(legacy_lo<center[13]-epsilon<center[13]+epsilon<legacy_hi,'legacy numerical enclosure')
    result={'passed':True,'dimension':N,'root_radius_interval':[str(center[13]-epsilon),str(center[13]+epsilon)],
        'half_width':str(epsilon),'residual_upper':str(Q(eta,S)),
        'contraction_norm_upper':str(Q(contraction,S)),
        'statement':'A unique real zero of the explicitly defined KKT system exists in this closed box; no global optimality claim.'}
    return result,box

if __name__=='__main__':
    negative='--negative-control' in sys.argv
    if negative:
        try:certify(True)
        except ValueError as exc:
            print(json.dumps({'passed':True,'negative_control':'perturbed radius rejected','reason':str(exc)}))
        else:raise ValueError('negative control unexpectedly accepted')
    else:
        result,_=certify()
        (HERE/'ROOT-CERTIFICATE.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result,indent=2))
