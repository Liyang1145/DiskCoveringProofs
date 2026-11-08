"""Diagnostic only: requires a not-yet-certified group lemma and angle transport."""
import math,sys,json,time
import numpy as np

U=float(sys.argv[1]) if len(sys.argv)>1 else .230001
KAPPA=float(sys.argv[2]) if len(sys.argv)>2 else .6
SHIFT=.06
A=3*math.sqrt(3)/4
BASE=min(A+.5-1.7604,(A+1-2.206)/2)
def huber(x):
    x=abs(x)
    return x*x if x<=.2 else .4*x-.04

for b in map(int,sys.argv[3:] or ['15','16','17','18']):
    started=time.time();T=50-b;D=3*T;H=3*b
    beta=math.pi-2*math.pi/b
    dp=np.full((D+1,H+1),np.inf);dp[0,0]=0
    for i in range(26):
        boundary=i<b
        nxt=np.full_like(dp,np.inf)
        for n in range(1 if boundary else 3,25 if boundary else 26):
            for h in range(2 if boundary else 0,min(2*n if boundary else n,H)+1):
                mean=(beta if boundary else 2*math.pi)/n-math.pi/3-SHIFT*((6 if boundary else 0)-2*h)/n
                cost=KAPPA*n*huber(mean)
                nxt[n:,h:]=np.minimum(nxt[n:,h:],dp[:D+1-n,:H+1-h]+cost)
        dp=nxt
    d=math.pi/b;s=math.sin(d)
    G=d-s*math.cos(d)+s*math.sqrt(U*U-s*s)
    gap=(50-b)*A*U*U+b*U*U/2+b*G-math.pi
    extra=float(dp[D,H])
    print(json.dumps({'U':U,'b':b,'kappa':KAPPA,'preferred_angle_shift':SHIFT,
        'corner_loss_proposal':extra,'base_edge_loss':b*BASE,
        'needed_total_loss':gap/(U*U),'net_regular_area_upper':gap-(extra+b*BASE)*U*U,
        'seconds':time.time()-started}),flush=True)
