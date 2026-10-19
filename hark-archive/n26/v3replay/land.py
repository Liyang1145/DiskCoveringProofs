import json,sys
from fractions import Fraction as F
import propose as PP, lgeom
tr,sl=lgeom.tree('304'); m,lo,hi=sl[0]
C=lgeom.C
import itertools
res=[]
for a,b,c in itertools.product([0,0.5,1],[0,0.5,1],[0,0.5,1]):
    p=list(C)
    for k,f in zip((12,13,14),(a,b,c)): p[k]=lo[k]+(hi[k]-lo[k])*F(f).limit_denominator(10)
    v,G,Fl=PP.propose(p,p)
    res.append(((a,b,c),v-float(PP.RUP)))
for r in sorted(res,key=lambda x:x[1]): print(r)
