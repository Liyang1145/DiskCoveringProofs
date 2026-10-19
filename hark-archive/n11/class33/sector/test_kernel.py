import time, random
from kernel import *
co=(F(0),F(30939859,10**9),F(41834891,10**9),F(1195057,250000000),F(-8660027,10**9),F(-605467,10**9))
B=((F(0),PIHI),(F(0),F(1)),(F(0),F(1)))
K=(F(0),F(2),F(0),F(39,100))
print('control valid',boundsValid(B,K),'bound',float(sectorDirectUpperQ(co,B,K)),'<=1/8?',sectorDirectUpperQ(co,B,K)<=F(1,8))
random.seed(1)
cf=tuple(float(x) for x in co)
t=time.time()
for _ in range(200):
    a0=random.uniform(0,3); u0=random.uniform(0,.9); v0=random.uniform(0,.9)
    w=random.choice([.3,.05,.01])
    Bq=((F(a0).limit_denominator(10**6),F(min(a0+w,3.1415)).limit_denominator(10**6)),(F(u0).limit_denominator(10**6),F(u0+w/3).limit_denominator(10**6)),(F(v0).limit_denominator(10**6),F(v0+w/3).limit_denominator(10**6)))
    b,K=leafBound(co,Bq)
    fb=fl_bound(cf,[float(x[0]) for x in Bq],[float(x[1]) for x in Bq])
    if b is None or abs(float(b)-fb)>1e-3: print('diff',float(b) if b is not None else None,fb,w)
print('time',time.time()-t)
